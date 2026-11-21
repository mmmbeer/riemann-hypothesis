import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KeepsCuspOfIsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveStabiliserCharacterDet
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDeterminantCongruentElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalVectorMemIdealCompletedLatticeIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitChineseRemainder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeStabilizerIffBasisIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdelicCoordinatesLatticeMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupMatrixIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameProductCharacterInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameCharacterFromProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLiftExists
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizer
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OnlySecondOfFormLaws
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol

section
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabInduce

section Abstract

variable {R L A : Type} [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup A]

theorem exists_induced (N : Submodule R L) (φ : L →+ A) (s : R → A →+ A) (H C : AddSubgroup A)
    (hφs : ∀ r a, φ (r • a) = s r (φ a)) (hs : ∀ r, ∀ z ∈ C, s r z ∈ C) (hφ : ∀ a, φ a ∈ H)
    (hN : ∀ a, φ a ∈ C ↔ a ∈ N) (hon : ∀ z ∈ H, ∃ a, z - φ a ∈ C)
    (k : A →+ A) (hks : ∀ r z, k (s r z) = s r (k z)) (hkH : ∀ z ∈ H, k z ∈ H) (hkC : ∀ z ∈ C, k z ∈ C) :
    ∃ f : (L ⧸ N) →ₗ[R] (L ⧸ N), ∀ a b, f (N.mkQ a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
  choose g hg using fun a => hon (k (φ a)) (hkH _ (hφ a))
  have key : ∀ a b, N.mkQ (g a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
    intro a b
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hN, map_sub]
    constructor
    · intro h
      have := add_mem (hg a) h
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h (hg a)
      rwa [sub_sub_sub_cancel_left] at this
  let g0 : L →ₗ[R] (L ⧸ N) :=
    { toFun := fun a => N.mkQ (g a)
      map_add' := fun a b => by
        rw [← map_add, key, map_add, map_add, map_add, add_sub_add_comm]
        exact add_mem (hg a) (hg b)
      map_smul' := fun r a => by
        rw [RingHom.id_apply, ← map_smul, key, hφs, hφs, hks, ← map_sub]
        exact hs r _ (hg a) }
  refine ⟨N.liftQ g0 fun a ha => ?_, fun a b => key a b⟩
  change N.mkQ (g a) = 0
  rw [← map_zero N.mkQ, key, map_zero, sub_zero]
  exact hkC _ ((hN a).2 ha)

theorem exists_induced_equiv (N : Submodule R L) (φ : L →+ A) (s : R → A →+ A) (H C : AddSubgroup A)
    (hφs : ∀ r a, φ (r • a) = s r (φ a)) (hs : ∀ r, ∀ z ∈ C, s r z ∈ C) (hφ : ∀ a, φ a ∈ H)
    (hN : ∀ a, φ a ∈ C ↔ a ∈ N) (hon : ∀ z ∈ H, ∃ a, z - φ a ∈ C)
    (k : A →+ A) (hks : ∀ r z, k (s r z) = s r (k z)) (hkH : ∀ z ∈ H, k z ∈ H) (hkC : ∀ z ∈ C, k z ∈ C)
    (k' : A →+ A) (hks' : ∀ r z, k' (s r z) = s r (k' z)) (hkH' : ∀ z ∈ H, k' z ∈ H) (hkC' : ∀ z ∈ C, k' z ∈ C)
    (h1 : ∀ z, k (k' z) = z) (h2 : ∀ z, k' (k z) = z) :
    ∃ γ : (L ⧸ N) ≃ₗ[R] (L ⧸ N), ∀ a b, γ (N.mkQ a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
  obtain ⟨f, hf⟩ := exists_induced N φ s H C hφs hs hφ hN hon k hks hkH hkC
  obtain ⟨f', hf'⟩ := exists_induced N φ s H C hφs hs hφ hN hon k' hks' hkH' hkC'
  refine ⟨LinearEquiv.ofLinearMap f f' ?_ ?_, hf⟩
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := N.mkQ_surjective q
    obtain ⟨b, hb⟩ := N.mkQ_surjective (f' (N.mkQ a))
    have h := neg_mem (hkC _ ((hf' a b).1 hb.symm))
    rw [map_sub, h1, neg_sub] at h
    rw [LinearMap.comp_apply, ← hb]
    exact (hf b a).2 h
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := N.mkQ_surjective q
    obtain ⟨b, hb⟩ := N.mkQ_surjective (f (N.mkQ a))
    have h := neg_mem (hkC' _ ((hf a b).1 hb.symm))
    rw [map_sub, h2, neg_sub] at h
    rw [LinearMap.comp_apply, ← hb]
    exact (hf' b a).2 h

end Abstract

section Space

variable {D : D7} (V : HSp D)

noncomputable def halfHom (b : 𝓞 D.host.E) :
    (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddMonoidHom.mk' (halfVec V b) fun _ _ => funext fun _ => mul_add _ _ _

theorem halfVec_eq (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V b z = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • z := rfl

theorem mulVec_halfVec (m : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) (b : 𝓞 D.host.E)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) : m *ᵥ halfVec V b z = halfVec V b (m *ᵥ z) := by
  rw [halfVec_eq, halfVec_eq, Matrix.mulVec_smul]

theorem map_closure_mem (I : Ideal (𝓞 D.host.E))
    (k : (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))
    (hks : ∀ r z, k (halfVec V r z) = halfVec V r (k z)) (hk : ∀ z ∈ latGHat V 1, k z ∈ latGHat V 1) :
    ∀ z ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z},
      k z ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z} := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, z, hz, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨b, hb, k z, hk z hz, hks b z⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

end Space

theorem exists_levGrp_induced : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ κ ∈ GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1, ∃ γ : GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.LevGrp Dw l, ∀ a : Dw.La, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (liftLa γ a)) ∈ AddSubgroup.closure {u | ∃ b ∈ l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z} := by
  intro D V H Dw l ι hι κ hκ
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hMmem : (l.M : 𝓞 D.host.E) ∈ l.Mb := by
    have h : (l.M : 𝓞 D.host.E) ∈ Ideal.span {(l.M : 𝓞 D.host.E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h
    exact Ideal.mul_le_left h
  have hMb : l.Mb ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hMmem
    exact hM0.ne' (Nat.cast_eq_zero.1 hMmem)
  have hκ1 : ∀ z ∈ latGHat V 1, (finHom V κ).1 *ᵥ z ∈ latGHat V 1 :=
    (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 hκ.2
  have hκ0 : ∀ z ∈ latHat V, (finHom V κ).1 *ᵥ z ∈ latHat V := by
    intro z hz
    obtain ⟨y, hy, e⟩ := hκ.2 z hz
    rw [one_smul, sub_eq_iff_eq_add] at e
    rw [e]
    exact add_mem hy hz
  have hκ2 : ∀ z ∈ latGHat V 1, (finHom V κ⁻¹).1 *ᵥ z ∈ latGHat V 1 :=
    (GlobalTheory.Member.AALev.congruences_agree D V κ⁻¹).1.2 fun z hz =>
      ⟨_, sub_mem (GlobalTheory.RecDict.finHom_inv_mulVec_mem V κ hκ0 z hz) hz, (one_smul _ _).symm⟩
  let φ : Dw.La →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun a => finVec V (ι a)) fun a b => by
      rw [map_add]
      exact GlobalTheory.Member.AALev.fv_add _ _
  have hmem : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have hsH : ∀ r, ∀ z ∈ latGHat V 1, halfHom V r z ∈ latGHat V 1 := by
    intro r z hz
    rw [hhat] at hz ⊢
    exact GlobalTheory.Member.AALev.hat_smul_int (latG V 1) r hz
  obtain ⟨γ, hγ⟩ := exists_induced_equiv (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) φ (halfHom V) (latGHat V 1)
    (AddSubgroup.closure {u | ∃ b ∈ l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z})
    (fun r a => by
      change finVec V (ι (r • a)) = _
      rw [map_smul]
      exact GlobalTheory.Member.AALev.fv_smul (r : D.host.E) (ι a))
    (fun r => map_closure_mem V l.Mb (halfHom V r) (fun _ _ => funext fun _ => mul_left_comm _ _ _) (hsH r))
    (fun a => by
      rw [hhat]
      exact GlobalTheory.Member.AALev.fv_mem_hat _ (hmem a))
    (fun a => by
      refine (GlobalTheory.T.rationalVector_mem_ideal_completedLattice_iff D V l.Mb hMb (ι a)).trans ?_
      rw [← hι.2, LinearMap.range_eq_map, ← Submodule.map_smul'']
      constructor
      · rintro ⟨x, hx, e⟩
        exact hι.1 e ▸ hx
      · exact fun h => ⟨a, h, rfl⟩)
    (fun z hz => by
      rw [hhat] at hz
      obtain ⟨x, hx, w, hw, e⟩ :=
        (GlobalTheory.AdLat.hat_rational_points_and_approx _ _ _ _ hfg hsp).2.1 l.M hM0 z hz
      rw [← hι.2] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [← hhat] at hw
      refine ⟨a, AddSubgroup.subset_closure ⟨_, hMmem, w, hw, ?_⟩⟩
      rw [e]
      refine (add_sub_cancel_left _ _).trans ?_
      rw [halfVec_eq, ← Nat.cast_smul_eq_nsmul (Af D.host.F ⊗[D.host.F] D.host.E)]
      congr 1
      exact (map_natCast ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F)
        (B := D.host.E)).toRingHom.comp (algebraMap (𝓞 D.host.E) D.host.E)) l.M).symm)
    (Matrix.mulVecLin (finHom V κ).1).toAddMonoidHom (mulVec_halfVec V _) hκ1
    (map_closure_mem V l.Mb _ (mulVec_halfVec V _) hκ1)
    (Matrix.mulVecLin (finHom V κ⁻¹).1).toAddMonoidHom (mulVec_halfVec V _) hκ2
    (map_closure_mem V l.Mb _ (mulVec_halfVec V _) hκ2)
    (fun z => by
      change (finHom V κ).1 *ᵥ ((finHom V κ⁻¹).1 *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, map_inv, Units.mul_inv, Matrix.one_mulVec])
    (fun z => by
      change (finHom V κ⁻¹).1 *ᵥ ((finHom V κ).1 *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec])
  exact ⟨γ, fun a => (hγ a _).1 (liftLa_spec γ a).symm⟩

end GlobalTheory.StabInduce
end

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_automorphism_mod_halfLevel : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ κ ∈ GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1, ∃ γ : GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.LevGrp Dw l, ∀ a : Dw.La, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (liftLa γ a)) ∈ AddSubgroup.closure {u | ∃ b ∈ l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z} := by
  atlas_forward_decl GlobalTheory.StabInduce.exists_levGrp_induced
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifEvery

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets (IsCover)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions (LevGrp levDet idealHat CongMod IsInvTame IsLevLift)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev iA (D : D7) (b : 𝓞 D.host.E) : Af D.host.F ⊗[D.host.F] D.host.E := (1 : Af D.host.F) ⊗ₜ (b : D.host.E)

theorem iA_mul (a b : 𝓞 D.host.E) : iA D (a * b) = iA D a * iA D b := by
  simp [iA, Algebra.TensorProduct.tmul_mul_tmul]

theorem iA_add (a b : 𝓞 D.host.E) : iA D (a + b) = iA D a + iA D b := by
  simp [iA, TensorProduct.tmul_add]

theorem iA_one : iA D 1 = 1 := by simp [iA, Algebra.TensorProduct.one_def]

theorem iA_nat (n : ℕ) : iA D n = n := by
  induction n with
  | zero => simp [iA]
  | succ n ih => rw [Nat.cast_succ, iA_add, ih, iA_one, Nat.cast_succ]

variable (V : HSp D)

def idl (I : Ideal (𝓞 D.host.E)) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z}

variable {V}

theorem halfVec_eq (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V b z = iA D b • z := rfl

theorem finVec_add (a b : Fin V.rank → D.host.E) : finVec V (a + b) = finVec V a + finVec V b :=
  GlobalTheory.Member.AALev.fv_add a b

theorem finVec_sub (a b : Fin V.rank → D.host.E) : finVec V (a - b) = finVec V a - finVec V b := by
  rw [eq_sub_iff_add_eq, ← finVec_add, sub_add_cancel]

theorem finVec_smul (b : 𝓞 D.host.E) (a : Fin V.rank → D.host.E) : finVec V (b • a) = iA D b • finVec V a :=
  GlobalTheory.Member.AALev.fv_smul (b : D.host.E) a

theorem smul_mem_hat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) {y : Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ intAE D) {z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    y • z ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    have h := GlobalTheory.Member.AALev.hat_smul_adele _ a ha (GlobalTheory.Member.AALev.hat_smul_int L x hz)
    rwa [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h
  | zero => rw [zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_smul]; exact neg_mem hx

theorem latGHat_one (V : HSp D) : latGHat V 1 = GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)) :=
  (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1

theorem smul_mem_latGHat {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D)
    {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ latGHat V 1) : y • z ∈ latGHat V 1 := by
  rw [latGHat_one] at hz ⊢
  exact smul_mem_hat _ hy hz

theorem smul_mem_latHat {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D)
    {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ latHat V) : y • z ∈ latHat V := by
  rw [GlobalTheory.Member.AALev.latHat_eq] at hz ⊢
  exact smul_mem_hat _ hy hz

theorem iA_mem (b : 𝓞 D.host.E) : iA D b ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, b, rfl⟩

theorem finVec_mem {a : Fin V.rank → D.host.E} (ha : a ∈ latG V 1) : finVec V a ∈ latGHat V 1 := by
  rw [latGHat_one]
  exact GlobalTheory.Member.AALev.fv_mem_hat _ ha

theorem smul_mem_idl {I : Ideal (𝓞 D.host.E)} {b : 𝓞 D.host.E} (hb : b ∈ I)
    {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ latGHat V 1) : iA D b • z ∈ idl V I :=
  AddSubgroup.subset_closure ⟨b, hb, z, hz, rfl⟩

theorem mem_levSet_one {κ : GA D V} :
    κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1 ↔ κ ∈ GfC V ∧ ∀ z ∈ latHat V, (finHom V κ).1 *ᵥ z ∈ latHat V := by
  refine and_congr Iff.rfl (forall₂_congr fun z hz => ⟨?_, fun h => ⟨_, sub_mem h hz, (one_smul _ _).symm⟩⟩)
  rintro ⟨y, hy, e⟩
  rw [one_smul, sub_eq_iff_eq_add] at e
  exact e ▸ add_mem hy hz

theorem finHom_mul (κ κ' : GA D V) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V (κ * κ')).1 *ᵥ z = (finHom V κ).1 *ᵥ ((finHom V κ').1 *ᵥ z) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem levSet_mul {κ κ' : GA D V} (h : κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1) (h' : κ' ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1) : κ * κ' ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1 := by
  rw [mem_levSet_one] at h h' ⊢
  exact ⟨mul_mem h.1 h'.1, fun z hz => finHom_mul κ κ' z ▸ h.2 _ (h'.2 z hz)⟩

theorem stab_latGHat {κ : GA D V} (h : κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1) {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ latGHat V 1) : (finHom V κ).1 *ᵥ z ∈ latGHat V 1 :=
  (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 h.2 z hz

theorem stab_idl {κ : GA D V} (h : κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1) {I : Ideal (𝓞 D.host.E)}
    {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ idl V I) : (finHom V κ).1 *ᵥ z ∈ idl V I := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, z, hz, rfl⟩ := hy
    rw [halfVec_eq, Matrix.mulVec_smul]
    exact smul_mem_idl hb (stab_latGHat h hz)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem smul_neg_eq {A : Type} [CommRing A] {n : ℕ} (b : A) (x w : Fin n → A) (M : ℕ) (e : b • x = M • w) :
    b • -x = M • -w := by rw [smul_neg, smul_neg, e]

theorem smul_idl_eq {I J : Ideal (𝓞 D.host.E)} {M : ℕ} (h : I * J = Ideal.span {(M : 𝓞 D.host.E)}) {b : 𝓞 D.host.E}
    (hb : b ∈ I) {u : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hu : u ∈ idl V J) :
    ∃ w ∈ latGHat V 1, iA D b • u = M • w := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b', hb', z, hz, rfl⟩ := hy
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.mul_mem_mul hb hb')
    refine ⟨iA D r • z, smul_mem_latGHat (iA_mem r) hz, ?_⟩
    rw [halfVec_eq, smul_smul, ← iA_mul, ← hr, mul_comm, iA_mul, iA_nat, mul_smul, Nat.cast_smul_eq_nsmul]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, e⟩ := hx
    obtain ⟨w', hw', e'⟩ := hy
    exact ⟨w + w', add_mem hw hw', by rw [smul_add, smul_add, e, e']⟩
  | neg x _ hx =>
    obtain ⟨w, hw, e⟩ := hx
    exact ⟨-w, neg_mem hw, smul_neg_eq _ _ _ _ e⟩

theorem inf_idl {I J : Ideal (𝓞 D.host.E)} {M : ℕ} (h : I * J = Ideal.span {(M : 𝓞 D.host.E)}) (hc : I ⊔ J = ⊤)
    {u : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hI : u ∈ idl V I) (hJ : u ∈ idl V J) :
    ∃ w ∈ latGHat V 1, u = M • w := by
  obtain ⟨m, hm, c, hc', e⟩ := Submodule.mem_sup.1 (hc ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ I ⊔ J)
  obtain ⟨w, hw, e1⟩ := smul_idl_eq h hm hJ
  obtain ⟨w', hw', e2⟩ := smul_idl_eq (mul_comm I J ▸ h) hc' hI
  refine ⟨w + w', add_mem hw hw', ?_⟩
  rw [smul_add, ← e1, ← e2, ← add_smul, ← iA_add, e, iA_one, one_smul]

section Lev

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H)

abbrev Mc : Ideal (𝓞 D.host.E) := l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)

theorem span_ne : Ideal.span {(l.M : 𝓞 D.host.E)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
  have := l.three_le
  omega

theorem Mb_ne : l.Mb ≠ ⊥ := fun h => span_ne l (by rw [← l.prod, h, Ideal.bot_mul])

theorem Mc_ne : Mc l ≠ ⊥ := fun h => span_ne l (by rw [← l.prod, show l.Mb.map _ = ⊥ from h, Ideal.mul_bot])

theorem M_mem : (l.M : 𝓞 D.host.E) ∈ l.Mb := by
  have h := Ideal.mem_span_singleton_self (l.M : 𝓞 D.host.E)
  rw [← l.prod] at h
  exact (Ideal.mul_le_inf h).1

theorem exists_split : ∃ m ∈ l.Mb, ∃ c ∈ Mc l, m + c = 1 :=
  Submodule.mem_sup.1 (by rw [show l.Mb ⊔ Mc l = ⊤ from l.coprime]; exact Submodule.mem_top)

variable (V) in

def Ind (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (γ : LevGrp Dw l) (κ : GA D V) : Prop :=
  κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1 ∧ ∀ a : Dw.La, (finHom V κ).1 *ᵥ finVec V (ι a) - finVec V (ι (liftLa γ a)) ∈ idl V l.Mb

variable {l} {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}

theorem iota_mem (hι : LatEmb V ι) (a : Dw.La) : finVec V (ι a) ∈ latGHat V 1 :=
  finVec_mem (hι.2 ▸ LinearMap.mem_range_self ι a)

theorem map_smul_top (hι : LatEmb V ι) (I : Ideal (𝓞 D.host.E)) :
    (I • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).map ι = I • latG V 1 := by
  rw [Submodule.map_smul'', Submodule.map_top, hι.2]

theorem iota_mem_idl (hι : LatEmb V ι) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (a : Dw.La) :
    finVec V (ι a) ∈ idl V I ↔ a ∈ I • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
  refine (GlobalTheory.T.rationalVector_mem_ideal_completedLattice_iff D V I hI (ι a)).trans ?_
  rw [← map_smul_top hι]
  exact ⟨fun ⟨b, hb, e⟩ => hι.1 e ▸ hb, fun h => ⟨a, h, rfl⟩⟩

theorem sub_mem_idl (hι : LatEmb V ι) (a a' : Dw.La) :
    finVec V (ι a) - finVec V (ι a') ∈ idl V l.Mb ↔
      (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a = (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a' := by
  rw [← finVec_sub, ← map_sub, iota_mem_idl hι (Mb_ne l), Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]

theorem Ind.unique (hι : LatEmb V ι) {γ γ' : LevGrp Dw l} {κ : GA D V} (h : Ind V l ι γ κ) (h' : Ind V l ι γ' κ) :
    γ = γ' := by
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [← liftLa_spec, ← liftLa_spec, ← sub_mem_idl hι]
  have := sub_mem (h'.2 a) (h.2 a)
  rwa [sub_sub_sub_cancel_left] at this

theorem Ind.mul (hι : LatEmb V ι) {γ γ' : LevGrp Dw l} {κ κ' : GA D V} (h : Ind V l ι γ κ) (h' : Ind V l ι γ' κ') :
    Ind V l ι (γ * γ') (κ * κ') := by
  refine ⟨levSet_mul h.1 h'.1, fun a => ?_⟩
  have h3 : finVec V (ι (liftLa γ (liftLa γ' a))) - finVec V (ι (liftLa (γ * γ') a)) ∈ idl V l.Mb := by
    rw [sub_mem_idl hι, liftLa_spec, liftLa_spec, liftLa_spec]
    rfl
  have := add_mem (add_mem (stab_idl h.1 (h'.2 a)) (h.2 (liftLa γ' a))) h3
  rw [Matrix.mulVec_sub, ← finHom_mul] at this
  convert this using 1
  abel

theorem nsmul_mem_idl {w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latGHat V 1) :
    l.M • w ∈ idl V l.Mb := by
  have := smul_mem_idl (M_mem l) hw
  rwa [iA_nat, Nat.cast_smul_eq_nsmul] at this

theorem ind_of_isLevLift (hι : LatEmb V ι) {γ : LevGrp Dw l} {κ : GA D V} (h : IsLevLift l V ι γ κ) :
    Ind V l ι γ κ := by
  have h1 : κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1 := mem_levSet_one.2 ⟨h.1, fun z hz => by
    have : (finHom V κ).1 *ᵥ z ∈ gLat V κ := ⟨z, hz, rfl⟩
    rwa [h.2.1] at this⟩
  refine ⟨h1, fun a => ?_⟩
  obtain ⟨m, hm, c, hc, e⟩ := exists_split l
  have e0 : (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ (c • liftLa γ a) =
      γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ (c • a)) := by
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearEquiv.map_smul, liftLa_spec]
  obtain ⟨w, hw, e1⟩ := h.2.2 (c • a) (Submodule.smul_mem_smul hc Submodule.mem_top) (c • liftLa γ a)
    (Submodule.smul_mem_smul hc Submodule.mem_top) e0
  have h0 := nsmul_mem_idl (l := l) hw
  rw [← e1, ι.map_smul, ι.map_smul, finVec_smul, finVec_smul, Matrix.mulVec_smul, ← smul_sub] at h0
  have h2 := add_mem (smul_mem_idl hm (sub_mem (stab_latGHat h1 (iota_mem hι a)) (iota_mem hι (liftLa γ a)))) h0
  rw [← add_smul, ← iA_add, e, iA_one, one_smul] at h2
  exact h2

theorem Ind.isLevLift (hι : LatEmb V ι) {γ : LevGrp Dw l} {κ : GA D V} (h : Ind V l ι γ κ) :
    IsLevLift l V ι γ κ := by
  have h1 := mem_levSet_one.1 h.1
  refine ⟨h1.1, ?_, fun a ha a' ha' e => ?_⟩
  · refine Set.Subset.antisymm ?_ fun z hz => ⟨_, GlobalTheory.RecDict.finHom_inv_mulVec_mem V κ h1.2 z hz, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact h1.2 z hz
    · show (finHom V κ).1 *ᵥ _ = z
      rw [← finHom_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  · refine inf_idl l.prod l.coprime ?_ ?_
    · have := add_mem (h.2 a) ((sub_mem_idl hι (liftLa γ a) a').2 (by rw [liftLa_spec, e]))
      rwa [sub_add_sub_cancel] at this
    · exact sub_mem (stab_idl h.1 ((iota_mem_idl hι (Mc_ne l) a).2 ha)) ((iota_mem_idl hι (Mc_ne l) a').2 ha')

theorem ind_one_of (hι : LatEmb V ι) {κ : GA D V} (h1 : κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1)
    (h : ∀ a, (finHom V κ).1 *ᵥ finVec V (ι a) - finVec V (ι a) ∈ idl V l.Mb) : Ind V l ι 1 κ := by
  refine ⟨h1, fun a => ?_⟩
  have := add_mem (h a) ((sub_mem_idl hι a (liftLa (1 : LevGrp Dw l) a)).2 (by rw [liftLa_spec]; rfl))
  rwa [sub_add_sub_cancel] at this

theorem ind_one_iff (hι : LatEmb V ι) {Kf : Subgroup (GA D V)} (hK : IsLevelK V l.M Kf) (hH : KfHalf V Kf l.M (Mc l))
    (κ : GA D V) : Ind V l ι 1 κ ↔ κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V l.M := by
  constructor
  · intro h
    refine (hK κ).1 ((hH κ).2 ⟨h.1.1, ((GlobalTheory.Member.AALev.congruences_agree D V κ).2 l.M (Mc l)).2 fun a ha => ?_⟩)
    rw [← map_smul_top hι] at ha
    obtain ⟨a, ha, rfl⟩ := ha
    exact (h.isLevLift hι).2.2 a ha a ha rfl
  · intro h
    refine ind_one_of hι ⟨h.1, fun z hz => ?_⟩ fun a => ?_
    · obtain ⟨y, hy, e⟩ := h.2 z hz
      exact ⟨l.M • y, nsmul_mem hy _, by rw [one_smul, e]⟩
    · obtain ⟨w, hw, e⟩ := ((GlobalTheory.Member.AALev.congruences_agree D V κ).2 l.M ⊤).1
        (fun b _ z hz => h.2 _ (smul_mem_latHat (iA_mem b) hz)) (ι a)
        (by rw [Submodule.top_smul, ← hι.2]; exact LinearMap.mem_range_self ι a)
      exact e ▸ nsmul_mem_idl hw

end Lev

section Char

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

variable {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}

variable {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ}

end Char

end GlobalTheory.UnifEvery
end
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_basis_hermitian_space : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r), ∃ β : GL (Fin r) (EAf D), LatticeBasisLifts.IsLatBasis V hr β := by
  first | exact @GlobalTheory.LatAdelicBasis.exists_isLatBasis | exact GlobalTheory.LatAdelicBasis.exists_isLatBasis | (intros; apply GlobalTheory.LatAdelicBasis.exists_isLatBasis <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedLattice_stabilizer_iff_basis_integral : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)), LatticeBasisLifts.IsLatBasis V hr β → ∀ κ : GA D V, gLat V κ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) ↔ LatticeBasisLifts.finR V hr κ ∈ Formalism.L2.DIV.St β := by
  first | exact @GlobalTheory.LatStab.gLat_eq_latHat_iff | exact GlobalTheory.LatStab.gLat_eq_latHat_iff | (intros; apply GlobalTheory.LatStab.gLat_eq_latHat_iff <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_adelic_coordinates_lattice_mod : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)), LatticeBasisLifts.IsLatBasis V hr β → ∀ (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ M : ℕ, 0 < M → ∃ ρ : La →+ (Fin r → LatticeBasisLifts.OAf D), (∀ (b : 𝓞 D.host.E) (a : La), ρ (b • a) = Formalism.L2.DIV.oToS D.host.F D.host.E b • ρ a) ∧ (∀ s : Fin r → LatticeBasisLifts.OAf D, ∃ (a : La) (s' : Fin r → LatticeBasisLifts.OAf D), s = ρ a + M • s') ∧ (∀ I J : Ideal (𝓞 D.host.E), I * J = Ideal.span {(M : 𝓞 D.host.E)} → ∀ a : La, (∀ i, ρ a i ∈ Formalism.L2.DIV.idS D.host.F I) → a ∈ I • (⊤ : Submodule (𝓞 D.host.E) La)) ∧ ∀ (κ : GA D V) (y : GL (Fin r) (LatticeBasisLifts.OAf D)), LatticeBasisLifts.finR V hr κ = Formalism.L2.DIV.frGL β y → ∀ a a' : La, (∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = M • w) ↔ ∃ s : Fin r → LatticeBasisLifts.OAf D, y.1.mulVec (ρ a) - ρ a' = M • s := by
  first | exact @GlobalTheory.GeoActCompare.exists_lattice_coord | exact GlobalTheory.GeoActCompare.exists_lattice_coord | (intros; apply GlobalTheory.GeoActCompare.exists_lattice_coord <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_group_matrix_isomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl E)), l.Mb = ∏ w ∈ Pg, w.asIdeal → ∀ (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (r : ℕ) (φ : LaMod Dw l ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ l.Mb)), ∃ ψ : Formalism.L2.DIV.G0 Pg r ≃* LevelLiftConditions.LevGrp Dw l, (∀ (g : Formalism.L2.DIV.G0 Pg r) (Y : Matrix (Fin r) (Fin r) (𝓞 E ⧸ l.Mb)), (∀ q, φ (ψ g q) = Y.mulVec (φ q)) ↔ ∀ w : ↥Pg, Y.map (Ideal.Quotient.factor (hle w)) = (g w).1) ∧ ∀ (g : Formalism.L2.DIV.G0 Pg r) (w : ↥Pg), Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom (LevelLiftConditions.levDet Dw l (ψ g)) = Matrix.GeneralLinearGroup.det (g w) := by
  first | exact @GlobalTheory.GeoActCompare.exists_levGrp_equiv_pi | exact GlobalTheory.GeoActCompare.exists_levGrp_equiv_pi | (intros; apply GlobalTheory.GeoActCompare.exists_levGrp_equiv_pi <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_product_character_inverse : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (K : Type) [Field K] (σ : K →+* ℂ) (μ : (AE D)ˣ →* Circle) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ), LatticeBasisLifts.IsInvTame σ Pg μ χ → LevelLiftConditions.IsInvTame σ l.Mb (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) μ (chiProd hle χ) := by
  first | exact @GlobalTheory.GeoActCompare.TameAB.isInvTame_chiProd | exact GlobalTheory.GeoActCompare.TameAB.isInvTame_chiProd | (intros; apply GlobalTheory.GeoActCompare.TameAB.isInvTame_chiProd <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_character_from_product : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (K : Type) [Field K] (σ : K →+* ℂ) (μ : (AE D)ˣ →* Circle) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ), (∀ x : (AE D)ˣ, cA D (x : AE D) = (x : AE D) → μ x = 1) → LevelLiftConditions.IsInvTame σ l.Mb (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) μ (chiProd hle χ) → LatticeBasisLifts.IsInvTame σ Pg μ χ := by
  first | exact @GlobalTheory.GeoActCompare.TameConj.isInvTame_of_half | exact GlobalTheory.GeoActCompare.TameConj.isInvTame_of_half | (intros; apply GlobalTheory.GeoActCompare.TameConj.isInvTame_of_half <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.FormTies (levFull)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rel

open CategoryTheory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem levR_congr {f g k : Dw.La →ₗ[𝓞 E] Dw.La}
    (h : ∀ a, f a - g a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : levR (f, k) y y' ↔ levR (g, k) y y' := by
  have e : ∀ a, Xo.univ.eta (f a) = Xo.univ.eta (g a) := fun a => by
    have h1 := Xo.univ.eta_add (g a) (f a - g a)
    rwa [add_sub_cancel, Xo.univ.eta_ker _ (h a), _root_.mul_one] at h1
  unfold levR IsLevMove
  simp only [e]

end Rel

section Half

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem exists_half (a : Dw.La) : ∃ b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
    (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ b = (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a := by
  have h : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [l.coprime, Submodule.top_smul]; trivial
  rw [Submodule.sup_smul] at h
  obtain ⟨x, hx, b, hb, rfl⟩ := Submodule.mem_sup.1 h
  refine ⟨b, hb, ?_⟩
  rw [map_add, show (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ x = 0 from (Submodule.Quotient.mk_eq_zero _).2 hx, zero_add]

theorem map_mem_smul_top {I : Ideal (𝓞 E)} (f : Dw.La →ₗ[𝓞 E] Dw.La) {a : Dw.La}
    (ha : a ∈ I • (⊤ : Submodule (𝓞 E) Dw.La)) : f a ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  have h := Submodule.mem_map_of_mem (f := f) ha
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem half_ne_bot (l : Level H) : l.Mb ≠ ⊥ := by
  intro h
  have h1 := l.prod
  rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
  have := l.three_le
  have h2 : l.M = 0 := by exact_mod_cast h1
  omega

theorem graph_iff {r : ℕ} (φ : LaMod Dw l ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ l.Mb)) (Y : Matrix (Fin r) (Fin r) (𝓞 E ⧸ l.Mb))
    (C : Dw.La → Dw.La → Prop)
    (hC : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), C a a' ↔
        φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a') = Y.mulVec (φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a)))
    (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) :
    (∀ q, φ (γ q) = Y.mulVec (φ q)) ↔
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a' = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a) → C a a' := by
  constructor
  · intro hg a ha a' ha' e
    rw [hC a ha a' ha', e, hg]
  · intro hg q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha, e⟩ := exists_half (l := l) x
    have ha' := map_mem_smul_top (liftLa γ) ha
    rw [← e, ← liftLa_spec]
    exact (hC a ha _ ha').1 (hg a ha _ ha' (liftLa_spec _ a))

theorem sub_liftLa_mem {r : ℕ} (φ : LaMod Dw l ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ l.Mb)) (Y : Matrix (Fin r) (Fin r) (𝓞 E ⧸ l.Mb))
    (C : Dw.La → Dw.La → Prop)
    (hC : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), C a a' ↔
        φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a') = Y.mulVec (φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a)))
    (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) (hγ : ∀ q, φ (γ q) = Y.mulVec (φ q)) (f : Dw.La →ₗ[𝓞 E] Dw.La)
    (hf : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), C a (f a)) (x : Dw.La) :
    f x - liftLa γ x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨a, ha, e⟩ := exists_half (l := l) x
  have e1 := (hC a ha _ (map_mem_smul_top f ha)).1 (hf a ha)
  rw [← hγ, φ.injective.eq_iff, e, ← liftLa_spec] at e1
  have e2 : f x - f a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [← map_sub]
    exact map_mem_smul_top f ((Submodule.Quotient.eq _).1 e.symm)
  have e3 := add_mem e2 ((Submodule.Quotient.eq _).1 e1)
  rwa [sub_add_sub_cancel] at e3

end Half

theorem exists_coord_of {O S La : Type} [CommRing O] [CommRing S] [AddCommGroup La] [Module O La] (o : O →+* S)
    {I J : Ideal O} {M r : ℕ} (hIJ : I * J = Ideal.span {(M : O)}) (hco : I ⊔ J = ⊤) (π : S →+* O ⧸ I)
    (hπ : ∀ a, π (o a) = Ideal.Quotient.mk I a) (hπ0 : ∀ s, π s = 0 ↔ s ∈ I.map o) (ρ : La →+ (Fin r → S))
    (hlin : ∀ (b : O) (a : La), ρ (b • a) = o b • ρ a)
    (hsur : ∀ s : Fin r → S, ∃ (a : La) (s' : Fin r → S), s = ρ a + M • s')
    (hker : ∀ a : La, (∀ i, ρ a i ∈ I.map o) → a ∈ I • (⊤ : Submodule O La)) :
    ∃ φ : (La ⧸ (I • (⊤ : Submodule O La))) ≃ₗ[O] (Fin r → O ⧸ I), ∀ y : Matrix (Fin r) (Fin r) S,
      ∀ a ∈ J • (⊤ : Submodule O La), ∀ a' ∈ J • (⊤ : Submodule O La),
        (∃ s : Fin r → S, y.mulVec (ρ a) - ρ a' = M • s) ↔
          φ ((I • (⊤ : Submodule O La)).mkQ a') = (y.map π).mulVec (φ ((I • (⊤ : Submodule O La)).mkQ a)) := by
  have hMb : (M : O) ∈ I :=
    Ideal.mul_le_left (I := I) (J := J) (by rw [hIJ]; exact Ideal.mem_span_singleton_self _)
  have hπM : ∀ s : S, π (M • s) = 0 := fun s => (hπ0 _).2 (by
    rw [nsmul_eq_mul, ← map_natCast o]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hMb))
  have hmem : ∀ K : Ideal O, ∀ a ∈ K • (⊤ : Submodule O La), ∀ i, ρ a i ∈ K.map o := fun K a ha i => by
    refine Submodule.smul_induction_on (p := fun a => ρ a i ∈ K.map o) ha ?_ ?_
    · intro b hb x _
      rw [hlin]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb)
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  let f : La →ₗ[O] (Fin r → O ⧸ I) :=
    { toFun := fun a i => π (ρ a i)
      map_add' := fun a b => funext fun i => by simp
      map_smul' := fun b a => funext fun i => by
        rw [hlin, Pi.smul_apply, smul_eq_mul, map_mul, hπ]
        rfl }
  have hk : LinearMap.ker f = I • (⊤ : Submodule O La) := by
    ext a
    rw [LinearMap.mem_ker]
    exact ⟨fun h => hker a fun i => (hπ0 _).1 (congrFun h i), fun h => funext fun i => (hπ0 _).2 (hmem _ a h i)⟩
  have hs : Function.Surjective f := fun x => by
    choose b hb using fun i => Ideal.Quotient.mk_surjective (x i)
    obtain ⟨a, s', e⟩ := hsur fun i => o (b i)
    refine ⟨a, funext fun i => ?_⟩
    have := congrArg π (congrFun e i)
    rw [Pi.add_apply, map_add, Pi.smul_apply, hπM, add_zero, hπ, hb] at this
    exact this.symm
  refine ⟨(Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs), fun y a ha a' ha' => ?_⟩
  change _ ↔ f a' = (y.map π).mulVec (f a)
  have hv : ∀ i, ((y.map π).mulVec (f a)) i = π (y.mulVec (ρ a) i) := fun i =>
    (RingHom.map_mulVec π y (ρ a) i).symm
  constructor
  · rintro ⟨s, e⟩
    funext i
    have := congrArg π (congrFun e i)
    rw [Pi.sub_apply, map_sub, Pi.smul_apply, hπM, sub_eq_zero] at this
    rw [hv]
    exact this.symm
  · intro e
    have h1 : ∀ i, (y.mulVec (ρ a) - ρ a') i ∈ Ideal.span {(M : S)} := fun i => by
      have hb : (y.mulVec (ρ a) - ρ a') i ∈ I.map o := by
        rw [← hπ0, Pi.sub_apply, map_sub, sub_eq_zero, ← hv, ← e]
        rfl
      have hc : (y.mulVec (ρ a) - ρ a') i ∈ J.map o := by
        refine sub_mem ?_ (hmem _ a' ha' i)
        exact Ideal.sum_mem _ (t := Finset.univ) (f := fun k => y i k * ρ a k) fun k _ =>
          Ideal.mul_mem_left _ _ (hmem _ a ha k)
      have hco' : I.map o ⊔ J.map o = ⊤ := by rw [← Ideal.map_sup, hco, Ideal.map_top]
      have hi := Submodule.mem_inf.2 ⟨hb, hc⟩
      rwa [← Ideal.mul_eq_inf_of_coprime hco', ← Ideal.map_mul, hIJ, Ideal.map_span, Set.image_singleton,
        map_natCast] at hi
    choose s hs using fun i => Ideal.mem_span_singleton'.1 (h1 i)
    exact ⟨s, funext fun i => by rw [← hs i, Pi.smul_apply, nsmul_eq_mul, mul_comm]⟩

theorem redAt_eq_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {r : ℕ}
    (β : GL (Fin r) (E ⊗[F] Formalism.L2.Herm.Af F)) {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) (w : Formalism.L2.DIV.Pl E) (hle : I ≤ w.asIdeal)
    (x : Formalism.L2.DIV.St β) (g : GL (Fin r) (Formalism.L2.DIV.kP w)) :
    Formalism.L2.DIV.redAt β w x = g ↔
      ((Formalism.L2.DIV.pullFr β x).1.map (resI F I hI)).map (Ideal.Quotient.factor hle) = g.1 := by
  rw [Units.ext_iff]
  refine Eq.congr_left ?_
  ext i k
  exact (factor_resI_eq_resS hI w hle _).symm

variable {D : D7}

section Dict

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

def Cong (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (M : ℕ) (κ : GA D V) (a a' : Dw.La) : Prop :=
  ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = M • w

set_option maxHeartbeats 800000 in

theorem exists_coord (l : Level H) (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D))
    (hβ : LatticeBasisLifts.IsLatBasis V hr β) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) :
    ∃ φ : LaMod Dw l ≃ₗ[𝓞 D.host.E] (Fin r → 𝓞 D.host.E ⧸ l.Mb),
      ∀ (κ : GA D V) (h : LatticeBasisLifts.finR V hr κ ∈ Formalism.L2.DIV.St β),
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        Cong V ι l.M κ a a' ↔
          φ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a') =
            ((Formalism.L2.DIV.pullFr β ⟨_, h⟩).1.map (resI D.host.F l.Mb (half_ne_bot l))).mulVec
              (φ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a)) := by
  obtain ⟨ρ, hlin, hsur, hker, hcong⟩ := GlobalTheory.T.exists_integral_adelic_coordinates_lattice_mod D V r hr β hβ Dw.La ι hι l.M (by have := l.three_le; omega)
  obtain ⟨φ, hφ⟩ := exists_coord_of (Formalism.L2.DIV.oToS D.host.F D.host.E) l.prod l.coprime
    (resI D.host.F l.Mb (half_ne_bot l)) (resI_oToS _ _) (resI_eq_zero_iff _ _) ρ hlin hsur (hker _ _ l.prod)
  refine ⟨φ, fun κ h a ha a' ha' => ?_⟩
  have h1 := hcong κ _ (Formalism.L2.DIV.frGL_pullFr β ⟨_, h⟩).symm a a'
  have h2 := hφ (Formalism.L2.DIV.pullFr β ⟨_, h⟩).1 a ha a' ha'
  have h3 := h1.trans h2
  exact h3

theorem exists_groupEquiv (l : Level H) (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D))
    (hβ : LatticeBasisLifts.IsLatBasis V hr β) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (hι : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀))
    (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (hP : l.Mb = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) :
    ∃ ψ : Formalism.L2.DIV.G0 Pg r ≃* LevelLiftConditions.LevGrp Dw l,
      (∀ g κ, LatticeBasisLifts.IsLift V hr β Pg g κ ↔
        LevelLiftConditions.IsLevLift l V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) (ψ g) κ) ∧
      (∀ (K : Type) [Field K] (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ) g,
        chiProd hle χ (LevelLiftConditions.levDet Dw l (ψ g)) = LatticeBasisLifts.chiDetG0 Pg r χ g) ∧
      (∀ g, LatticeBasisLifts.Induces Dw l V hr ι₀ β Pg g (liftLa (ψ g))) ∧
      ∀ g γ, (∃ κ, LatticeBasisLifts.IsLift V hr β Pg g κ) → LatticeBasisLifts.Induces Dw l V hr ι₀ β Pg g γ →
        ∀ a, γ a - liftLa (ψ g) a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
  obtain ⟨φ, hφ⟩ := exists_coord l V hr β hβ _ hι
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.T.level_group_matrix_isomorphism D.host.E H Dw l Pg hP hle r φ
  have hred : ∀ (g : Formalism.L2.DIV.G0 Pg r) (x : Formalism.L2.DIV.St β),
      (∀ w : ↥Pg, Formalism.L2.DIV.redAt β w.1 x = g w) ↔
        ∀ q, φ (ψ g q) = ((Formalism.L2.DIV.pullFr β x).1.map (resI D.host.F l.Mb (half_ne_bot l))).mulVec (φ q) := by
    intro g x
    have e1 := h1 g ((Formalism.L2.DIV.pullFr β x).1.map (resI D.host.F l.Mb (half_ne_bot l)))
    have e2 := fun w : ↥Pg => redAt_eq_iff β (half_ne_bot l) w.1 (hle w) x (g w)
    exact ⟨fun h => e1.2 fun w => (e2 w).1 (h w), fun h w => (e2 w).2 (e1.1 h w)⟩
  have hlift : ∀ g κ, LatticeBasisLifts.IsLift V hr β Pg g κ ↔
      LevelLiftConditions.IsLevLift l V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) (ψ g) κ := by
    intro g κ
    have hst := GlobalTheory.T.completedLattice_stabilizer_iff_basis_integral D V r hr β hβ κ
    have hgr := fun h => (hred g ⟨_, h⟩).trans (graph_iff φ _ _ (hφ κ h) (ψ g))
    exact and_congr_right fun _ =>
      ⟨fun ⟨h, hg⟩ => ⟨hst.2 h, (hgr h).1 hg⟩, fun ⟨h, hg⟩ => ⟨hst.1 h, (hgr (hst.1 h)).2 hg⟩⟩
  refine ⟨ψ, hlift, fun K _ χ g => ?_, fun g κ hκ a ha => ?_, fun g γ ⟨κ, hκ⟩ hγ => ?_⟩
  · rw [chiProd_apply, LatticeBasisLifts.chiDetG0_apply]
    exact Finset.prod_congr rfl fun w _ => congrArg (χ w) (h2 g w)
  · exact ((hlift g κ).1 hκ).2.2 a ha _ (map_mem_smul_top _ ha) (liftLa_spec _ a)
  · obtain ⟨h, hg⟩ := hκ.2
    have h3 := sub_liftLa_mem φ _ _ (hφ κ h) (ψ g) ((hred g ⟨_, h⟩).1 hg) γ
    exact h3 (hγ κ hκ)

theorem act_transport {Xo : Moduli Dw l} (c : Coeff l) {G : Type} [Group G] (ψ : G ≃* LevelLiftConditions.LevGrp Dw l)
    (γ : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La)
    (h : ∀ g a, γ g a - liftLa (ψ g) a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    (∀ g, actLev (Xo := Xo) c (LatticeBasisLifts.levOf γ) g = actLev (Xo := Xo) c (levFull Dw l) (ψ g)) ∧
      (ActLev (Xo := Xo) c (LatticeBasisLifts.levOf γ) ↔ ActLev (Xo := Xo) c (levFull Dw l)) := by
  have key : ∀ (g : G) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S),
      levActR (Xo := Xo) (c := c) (LatticeBasisLifts.levOf γ) g y y' ↔ levActR (Xo := Xo) (c := c) (levFull Dw l) (ψ g) y y' :=
    fun g S _ _ y y' => levR_congr (h g) y y'
  have key' : ∀ (g : LevelLiftConditions.LevGrp Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S),
      levActR (Xo := Xo) (c := c) (levFull Dw l) g y y' ↔
        levActR (Xo := Xo) (c := c) (LatticeBasisLifts.levOf γ) (ψ.symm g) y y' := fun g S _ _ y y' => by
    rw [key, ψ.apply_symm_apply]
  refine ⟨fun g => ?_, fun L => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun L => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · refine LinearMap.ext fun f => funext fun p => funext fun y => ?_
    have e : (fun y' => levActR (Xo := Xo) (c := c) (LatticeBasisLifts.levOf γ) g y y') =
        fun y' => levActR (Xo := Xo) (c := c) (levFull Dw l) (ψ g) y y' := funext fun y' => propext (key g y y')
    have gen : ∀ P Q : FrPt Xo c p.R → Prop, P = Q → (open Classical in if h : ∃ y', P y' then h.choose else y) =
        (open Classical in if h : ∃ y', Q y' then h.choose else y) := fun P Q e => by subst e; rfl
    exact congrArg (f p) (gen _ _ e)
  · intro g S _ _ y
    simpa only [key'] using L.total (ψ.symm g) S y
  · intro g S _ _ y y' y'' a b
    exact L.func _ S y y' y'' ((key' _ _ _).1 a) ((key' _ _ _).1 b)
  · intro S _ _ y
    refine (key' 1 y y).2 ?_
    rw [map_one]
    exact L.one S y
  · intro g k S _ _ y y' y'' a b
    refine (key' _ _ _).2 ?_
    rw [map_mul]
    exact L.mul _ _ S y y' y'' ((key' _ _ _).1 a) ((key' _ _ _).1 b)
  · intro g S T _ _ _ _ φ y y' z z' m a b
    exact L.nat _ S T φ y y' z z' m ((key' _ _ _).1 a) ((key' _ _ _).1 b)
  · intro g S _ _ t y y' z z' m a b
    exact L.bor _ S t y y' z z' m ((key' _ _ _).1 a) ((key' _ _ _).1 b)
  · intro g S _ _ y
    simpa only [key] using L.total (ψ g) S y
  · intro g S _ _ y y' y'' a b
    exact L.func _ S y y' y'' ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro S _ _ y
    refine (key 1 y y).2 ?_
    rw [map_one]
    exact L.one S y
  · intro g k S _ _ y y' y'' a b
    refine (key _ _ _).2 ?_
    rw [map_mul]
    exact L.mul _ _ S y y' y'' ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro g S T _ _ _ _ φ y y' z z' m a b
    exact L.nat _ S T φ y y' z z' m ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro g S _ _ t y y' z z' m a b
    exact L.bor _ S t y y' z z' m ((key _ _ _).1 a) ((key _ _ _).1 b)

end Dict

theorem readAd_eq (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (c : (T.U j σ).Comp → ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (f : T.R j) (h : GA D (T.V j σ)) :
    LatticeBasisLifts.readAd T.toCore j σ c a f h = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * LevelLiftConditions.adFn T j σ c f h := rfl

theorem laws_iff (T : CoreJ D) (j : ℕ) (β : GL (Fin D.R.r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* (T.Q.c.F)ˣ) (χ' : (𝓞 D.host.E ⧸ T.Q.l.Mb)ˣ →* (T.Q.c.F)ˣ)
    (ψ : Formalism.L2.DIV.G0 Pg D.R.r ≃* LevelLiftConditions.LevGrp (T.Q.Dw j) T.Q.l)
    (hl : ∀ σ, GoodEmb T.Q.c σ → ∀ (hr : (T.V j σ).rank = D.R.r) g κ, LatticeBasisLifts.IsLift (T.V j σ) hr β Pg g κ ↔
      LevelLiftConditions.IsLevLift T.Q.l (T.V j σ) (LevelLiftConditions.iotaAt T j σ hr) (ψ g) κ)
    (hχ : ∀ g, χ' (LevelLiftConditions.levDet _ _ (ψ g)) = LatticeBasisLifts.chiDetG0 Pg D.R.r χ g)
    (γ : Formalism.L2.DIV.G0 Pg D.R.r → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)
    (hγ : ∀ g a, γ g a - liftLa (ψ g) a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) :
    LatticeBasisLifts.LevelActionLaws T j β Pg χ γ ↔ LevelLiftConditions.GeoActAt T j χ' := by
  obtain ⟨h1, h2⟩ := act_transport (Xo := T.Q.Xo j) T.Q.c ψ γ hγ
  have hg : ∀ g, LatticeBasisLifts.geoAct T.toCore j γ g = LevelLiftConditions.geo T j (ψ g) := h1
  have h0 : ∀ a, (lieFac (T.Q.Dw j) (xiR D) a : ℂ) ≠ 0 := fun a => Complex.ofReal_ne_zero.2 (lieFac_pos _ _ _).ne'
  constructor
  · intro L
    refine ⟨h2.1 L.act, fun a n hd g => ?_, fun σ hσ hr g => ?_, fun σ hσ hr n hn => ?_, fun a n hd g => ?_⟩
    · obtain ⟨g, rfl⟩ := ψ.surjective g
      exact hg g ▸ L.cusp a n hd g
    · obtain ⟨g, rfl⟩ := ψ.surjective g
      exact (L.lift σ hσ hr g).imp fun κ => (hl σ hσ hr g κ).1
    · obtain ⟨c, hc, H⟩ := L.read σ hσ hr n hn
      refine ⟨c, hc, fun a hd f hf g κ hκ x => ?_⟩
      obtain ⟨g, rfl⟩ := ψ.surjective g
      have e := H a hd g κ ((hl σ hσ hr g κ).2 hκ) f hf x
      rw [readAd_eq, readAd_eq, hg, ← hχ, mul_left_comm] at e
      exact mul_left_cancel₀ (h0 a) e
    · obtain ⟨g, rfl⟩ := ψ.surjective g
      exact hg g ▸ L.integral a n hd g
  · intro L
    refine ⟨h2.2 L.laws, fun a n hd g => ?_, fun σ hσ hr g => ?_, fun σ hσ hr n hn => ?_, fun a n hd g => ?_⟩
    · exact hg g ▸ L.keeps a n hd (ψ g)
    · exact (L.lifts σ hσ hr (ψ g)).imp fun κ => (hl σ hσ hr g κ).2
    · obtain ⟨c, hc, H⟩ := L.equiv σ hσ hr n hn
      refine ⟨c, hc, fun a hd g κ hκ f hf x => ?_⟩
      rw [readAd_eq, readAd_eq, hg, H a hd f hf (ψ g) κ ((hl σ hσ hr g κ).1 hκ) x, hχ, mul_left_comm]
    · exact hg g ▸ L.integral a n hd (ψ g)

theorem half_eq_prod {T : CoreJ D} (hT : LawsJ T) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hPg : ∀ w, w ∈ Pg ↔ T.Q.l.Mb ≤ w.asIdeal) : T.Q.l.Mb = ∏ w ∈ Pg, w.asIdeal := by
  refine GlobalTheory.CoverHalf.eq_prod_of_squarefree ?_ Pg hPg
  have h := GlobalTheory.CoverHalf.squarefree_span_g D
  rw [← hT.pins.2.1.1, ← T.Q.l.prod] at h
  exact h.of_mul_left

theorem chiW_fixed {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) (x : (AE D)ˣ) (hx : cA D (x : AE D) = x) :
    T.chiW j T.σ₀ x = 1 := by
  have h := (hT.muVal j hj T.σ₀ T.toCore.good_σ₀).2 1
  have hroot : ∀ y : (AE D)ˣ, cA D (y : AE D) = y → IsDetRoot (T.V j T.σ₀) 1 y := fun y hy => by
    unfold IsDetRoot
    rw [map_one, Units.val_one, Matrix.det_one, one_mul]
    exact hy.symm
  have e := (h x (hroot x hx)).symm.trans (h 1 (hroot 1 (by rw [Units.val_one, map_one])))
  rw [map_one] at e
  exact Circle.ext e

theorem isInvTame_iff {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hle : ∀ w : ↥Pg, T.Q.l.Mb ≤ w.1.asIdeal) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* (T.Q.c.F)ˣ) :
    LatticeBasisLifts.IsInvTame T.toCore.σ₀ Pg (T.chiW j T.toCore.σ₀) χ ↔
      LevelLiftConditions.IsInvTame T.σ₀ T.Q.l.Mb (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) (T.chiW j T.σ₀)
        (chiProd hle χ) :=
  ⟨GlobalTheory.T.tame_product_character_inverse D T.Q.H T.Q.l Pg hle _ _ _ χ, GlobalTheory.T.tame_character_from_product D T.Q.H T.Q.l Pg hle _ _ _ χ (chiW_fixed hT hj)⟩

theorem conclusion_iff {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) (hr : (D.sp.W j).rank = D.R.r)
    {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (hPg : ∀ w, w ∈ Pg ↔ T.Q.l.Mb ≤ w.asIdeal) (β : GL (Fin D.R.r) (EAf D))
    (hβ : LatticeBasisLifts.IsLatBasis (D.sp.W j) hr β) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* (T.Q.c.F)ˣ) :
    ((∀ g, ∃ γ₀, LatticeBasisLifts.Induces (T.Q.Dw j) T.Q.l (D.sp.W j) hr (T.iota j) β Pg g γ₀) ∧
      ∀ γ : Formalism.L2.DIV.G0 Pg D.R.r → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La,
        (∀ g, LatticeBasisLifts.Induces (T.Q.Dw j) T.Q.l (D.sp.W j) hr (T.iota j) β Pg g (γ g)) →
          LatticeBasisLifts.LevelActionLaws T j β Pg χ γ) ↔
      LevelLiftConditions.GeoActAt T j (chiProd (fun w => (hPg w.1).1 w.2) χ) := by
  have hV := hT.spaceW j hj
  have hι : LatEmb (D.sp.W j) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) := by
    obtain ⟨hr₀, -, -, -, -, -, -, h, -⟩ := hT.adPin j hj T.σ₀ T.toCore.good_σ₀
    have gen : ∀ (V : HSp D) (hV : V.rank = D.R.r), V = D.sp.W j →
        LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hV) ∘ₗ T.iota j) →
        LatEmb (D.sp.W j) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) := by
      rintro V _ rfl h
      exact h
    exact gen _ hr₀ (hV _ T.toCore.good_σ₀) h
  obtain ⟨ψ, h1, h2, h3, h4⟩ := exists_groupEquiv T.Q.l (D.sp.W j) hr β hβ (T.iota j) hι Pg (half_eq_prod hT hPg)
    (fun w => (hPg w.1).1 w.2)
  have gen : ∀ (V : HSp D) (hV : V.rank = D.R.r), V = D.sp.W j →
      (∀ g κ, LatticeBasisLifts.IsLift V hV β Pg g κ ↔ LevelLiftConditions.IsLevLift T.Q.l V
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hV) ∘ₗ T.iota j) (ψ g) κ) ∧
      ∀ g, (∃ κ, LatticeBasisLifts.IsLift V hV β Pg g κ) → ∃ κ, LatticeBasisLifts.IsLift (D.sp.W j) hr β Pg g κ := by
    rintro V _ rfl
    exact ⟨h1, fun _ h => h⟩
  have hiff := laws_iff T j β Pg χ _ ψ (fun σ hσ hr' => (gen _ hr' (hV σ hσ)).1) (h2 _ χ)
  constructor
  · rintro ⟨-, H⟩
    exact (hiff _ fun g a => by rw [sub_self]; exact zero_mem _).1 (H (fun g => liftLa (ψ g)) h3)
  · intro L
    refine ⟨fun g => ⟨_, h3 g⟩, fun γ hγ => (hiff γ fun g => h4 g _ ?_ (hγ g)).2 L⟩
    have hr₀ : (T.V j T.σ₀).rank = D.R.r := by rw [hV _ T.toCore.good_σ₀]; exact hr
    have G := gen _ hr₀ (hV _ T.toCore.good_σ₀)
    exact G.2 g ((L.lifts T.σ₀ T.toCore.good_σ₀ hr₀ (ψ g)).imp fun κ => (G.1 g κ).2)

theorem at_iff {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) :
    (∀ (hr : (D.sp.W j).rank = D.R.r) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)),
      (∀ w, w ∈ Pg ↔ T.Q.l.Mb ≤ w.asIdeal) →
      ∀ β : GL (Fin D.R.r) (EAf D), LatticeBasisLifts.IsLatBasis (D.sp.W j) hr β →
      ∀ χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* (T.Q.c.F)ˣ,
        LatticeBasisLifts.IsInvTame T.toCore.σ₀ Pg (T.chiW j T.toCore.σ₀) χ →
        (∀ g, ∃ γ₀, LatticeBasisLifts.Induces (T.Q.Dw j) T.Q.l (D.sp.W j) hr (T.iota j) β Pg g γ₀) ∧
        ∀ γ : Formalism.L2.DIV.G0 Pg D.R.r → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La,
          (∀ g, LatticeBasisLifts.Induces (T.Q.Dw j) T.Q.l (D.sp.W j) hr (T.iota j) β Pg g (γ g)) →
            LatticeBasisLifts.LevelActionLaws T j β Pg χ γ) ↔
    ∀ χ : (𝓞 D.host.E ⧸ T.Q.l.Mb)ˣ →* (T.Q.c.F)ˣ,
      LevelLiftConditions.IsInvTame T.σ₀ T.Q.l.Mb (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) (T.chiW j T.σ₀) χ →
        LevelLiftConditions.GeoActAt T j χ := by
  constructor
  · intro H χ' hχ'
    have hr : (D.sp.W j).rank = D.R.r := D.sp.W_rank j hj.1 hj.2
    obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_lattice_basis_hermitian_space D (D.sp.W j) _ hr
    let Pg := (Ideal.finite_factors (I := T.Q.l.Mb) (half_ne_bot T.Q.l)).toFinset
    have hPg : ∀ w, w ∈ Pg ↔ T.Q.l.Mb ≤ w.asIdeal := fun w => by
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_iff_le
    obtain ⟨χ, rfl⟩ := exists_chiProd_eq (half_eq_prod hT hPg) (fun w => (hPg w.1).1 w.2) χ'
    exact (conclusion_iff hT hj hr hPg β hβ χ).1 (H hr Pg hPg β hβ χ ((isInvTame_iff hT hj _ χ).2 hχ'))
  · intro H hr Pg hPg β hβ χ hχ
    exact (conclusion_iff hT hj hr hPg β hβ χ).2 (H _ ((isInvTame_iff hT hj _ χ).1 hχ))


end GlobalTheory.GeoActCompare
end
end

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LevelReduction

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open Formalism.L2.DIV (oToS idS frGL St pullFr)
open Formalism.IndefR.Lev (finE swapAE EAf)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevSplit GlobalTheory.IdemSupport GlobalTheory.ParahoricLift GlobalTheory.GeoActCompare
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_gen_pow {E : Type} [Field E] [NumberField E] {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) :
    ∃ x ∈ I, x ≠ 0 ∧ ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ Q.asIdeal → I ≤ Q.asIdeal := by
  let J : nonZeroDivisors (Ideal (𝓞 E)) := ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩
  obtain ⟨h, hh, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite (ClassGroup.mk0 J))
  rw [← map_pow] at e
  obtain ⟨x, hx⟩ : (I ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff (J ^ h).2).1 e
  have hx' : I ^ h = Ideal.span {x} := hx
  refine ⟨x, Ideal.pow_le_self hh.ne' (hx' ▸ Ideal.mem_span_singleton_self x), ?_, fun Q hQ => ?_⟩
  · rintro rfl
    exact pow_ne_zero h hI (by rw [hx']; simp)
  · have := Q.isPrime
    exact Ideal.IsPrime.le_of_pow_le (hx'.le.trans ((Ideal.span_singleton_le_iff_mem _).2 hQ))

theorem map_eq_of_smul_eq {A T : Type} [CommRing A] [CommRing T] {n : ℕ} (S : Subring A) (β : GL (Fin n) A)
    (ψ : S →+* T) (p : S) (hp : ψ p = 1) (y Y : Matrix (Fin n) (Fin n) S)
    (hx : (p : A) • (β.1 * y.map S.subtype * (β⁻¹).1) = (p : A) • (β.1 * Y.map S.subtype * (β⁻¹).1)) :
    y.map ψ = Y.map ψ := by
  have h2 := congrArg (fun M => (β⁻¹).1 * M * β.1) hx
  simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] at h2
  ext i j
  have h3 : p * y i j = p * Y i j := Subtype.ext (congrFun (congrFun h2 i) j)
  have h4 := congrArg ψ h3
  rw [map_mul, map_mul, hp, one_mul, one_mul] at h4
  exact h4

theorem map_eq_one_of_sub {R A T : Type} [CommRing R] [CommRing A] [CommRing T] (S : Subring A) (f : R →+* A)
    (ψ : S →+* T) {e : R} {p w x : S} (hp : (p : A) = f e) (hw : (w : A) * x = f (1 - e)) (hx : ψ x = 0) : ψ p = 1 := by
  have h6 : 1 - p = w * x := Subtype.ext (by
    show (1 : A) - p = w * x
    rw [hw, map_sub, map_one, hp])
  have h7 := congrArg ψ h6
  rw [map_mul, hx, mul_zero, map_sub, map_one, sub_eq_zero] at h7
  exact h7.symm

theorem exists_matrix {O : Type} [CommRing O] (I : Ideal O) {n : ℕ} (f : (Fin n → O ⧸ I) ≃ₗ[O] (Fin n → O ⧸ I)) :
    ∃ Y : Matrix (Fin n) (Fin n) O, IsUnit (Ideal.Quotient.mk I Y.det) ∧
      ∀ x, f x = Y.map (Ideal.Quotient.mk I) *ᵥ x := by
  let g : (Fin n → O ⧸ I) ≃ₗ[O ⧸ I] (Fin n → O ⧸ I) := f.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  choose M hM using fun i j => Ideal.Quotient.mk_surjective (LinearMap.toMatrix' g.toLinearMap i j)
  have e : Matrix.map (Matrix.of M) (Ideal.Quotient.mk I) = LinearMap.toMatrix' g.toLinearMap := Matrix.ext hM
  refine ⟨Matrix.of M, ?_, fun x => ?_⟩
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, e, LinearMap.det_toMatrix']
    exact g.isUnit_det'
  · rw [e, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl

variable {D : D7}

theorem exists_div {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {e : AE D} (he : e * e = e)
    {d : 𝓞 D.host.E} (d0 : d ≠ 0) (hd : ∀ Q, Φ e Q ≠ 0 → d ∉ Q.asIdeal) :
    ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (u : EAf D) * (oToS D.host.F D.host.E d : Formalism.L2.Herm.intAf D.host.F D.host.E) = finSw D e := by
  refine ⟨⟨_, swapAE_int (not_not.1 fun hn => ?_ : finPart D (e * incA D ((d : D.host.E)⁻¹)) ∈ intAE D)⟩, ?_⟩
  · obtain ⟨Q, h1, h2⟩ := (not_int_iff hΦ he d0).1 hn
    exact hd Q h1 h2
  · show finSw D (e * incA D ((d : D.host.E)⁻¹)) * finSw D (incA D (d : D.host.E)) = _
    have : (d : D.host.E) ≠ 0 := by simpa using d0
    rw [← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ this, RingHom.map_one, mul_one]

theorem exists_idem_finset {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ)
    (T : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hT : ∀ P ∈ T, cP P ∉ T) :
    ∃ e : AE D, infPart D e = 0 ∧ (∀ Q ∈ T, Φ e Q = 1) ∧ (∀ Q ∉ T, Φ e Q = 0) ∧ ∀ Q ∈ T, Φ (cA D e) Q = 0 := by
  classical
  choose δ hδ using exists_delta hΦ
  have ev : ∀ (f : HeightOneSpectrum (𝓞 D.host.E) → AE D) (s : Finset (HeightOneSpectrum (𝓞 D.host.E))) Q,
      Φ (∑ P ∈ s, f P) Q = ∑ P ∈ s, Φ (f P) Q := by
    intro f s Q
    induction s using Finset.cons_induction with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, ev_zero]
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ev_add, ih]
  refine ⟨∑ P ∈ T, δ P, ?_, fun Q hQ => ?_, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · rw [map_sum]
    exact Finset.sum_eq_zero fun P _ => (hδ P).1
  · rw [ev, Finset.sum_eq_single_of_mem Q hQ fun P _ h => (hδ P).2.2 Q h.symm, (hδ Q).2.1]
  · rw [ev]
    exact Finset.sum_eq_zero fun P hP => (hδ P).2.2 Q fun h => hQ (h ▸ hP)
  · rw [map_sum, ev]
    exact Finset.sum_eq_zero fun P hP => (delta_conj hΦ (hδ P)).2.2 Q fun h => hT P hP (h ▸ hQ)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

theorem exists_half_idem (l : Level H) :
    ∃ (e : AE D) (p : Formalism.L2.Herm.intAf D.host.F D.host.E), e * e = e ∧ e * cA D e = 0 ∧ infPart D e = 0 ∧
      (p : EAf D) = finSw D e ∧ resI D.host.F l.Mb (half_ne_bot l) p = 1 ∧
      ∀ d : 𝓞 D.host.E, IsUnit (Ideal.Quotient.mk l.Mb d) → ∃ u, u * oToS D.host.F D.host.E d = p := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hT : ∀ Q, Q ∈ (Ideal.finite_factors (half_ne_bot l)).toFinset ↔ l.Mb ≤ Q.asIdeal := fun Q => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le]
  generalize (Ideal.finite_factors (half_ne_bot l)).toFinset = T at hT
  obtain ⟨e, h0, h1, h2, h3⟩ := exists_idem_finset hΦ T fun P hP hP' =>
    GlobalTheory.GeoLevel.not_isConjPl_of_le l ((hT _).1 hP) ((hT _).1 hP') ((isConjPl_iff _ _).2 rfl)
  have he : e * e = e := hΦ.ext' (by rw [map_mul, h0, mul_zero]) fun Q => by
    rw [ev_mul]
    by_cases hQ : Q ∈ T
    · rw [h1 Q hQ, mul_one]
    · rw [h2 Q hQ, mul_zero]
  have he' : e * cA D e = 0 := hΦ.ext' (by rw [map_mul, h0, zero_mul, map_zero]) fun Q => by
    rw [ev_mul, ev_zero]
    by_cases hQ : Q ∈ T
    · rw [h3 Q hQ, mul_zero]
    · rw [h2 Q hQ, zero_mul]
  have hdiv : ∀ d : 𝓞 D.host.E, IsUnit (Ideal.Quotient.mk l.Mb d) → ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (u : EAf D) * (oToS D.host.F D.host.E d : Formalism.L2.Herm.intAf D.host.F D.host.E) = finSw D e := by
    intro d hd
    have hd' : ∀ Q ∈ T, d ∉ Q.asIdeal := fun Q hQ h => by
      have h4 := hd.map (Ideal.Quotient.factor ((hT Q).1 hQ))
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 h] at h4
      have := Q.isPrime
      exact not_isUnit_zero h4
    by_cases d0 : d = 0
    · have : e = 0 := hΦ.ext' (h0.trans (map_zero _).symm) fun Q => by
        rw [ev_zero, h2 Q fun hQ => hd' Q hQ (d0 ▸ zero_mem _)]
      exact ⟨0, by rw [this, map_zero, ZeroMemClass.coe_zero, zero_mul]⟩
    · exact exists_div hΦ he d0 fun Q hQ => hd' Q (by_contra fun h => hQ (h2 Q h))
  obtain ⟨u, hu⟩ := hdiv 1 (by rw [map_one]; exact isUnit_one)
  obtain ⟨p, hp⟩ : ∃ p : Formalism.L2.Herm.intAf D.host.F D.host.E, (p : EAf D) = finSw D e :=
    ⟨u * oToS D.host.F D.host.E 1, hu⟩
  refine ⟨e, p, he, he', h0, hp, ?_, fun d hd => ?_⟩
  · obtain ⟨x, hx, x0, hxQ⟩ := exists_gen_pow (half_ne_bot l)
    obtain ⟨w, hw⟩ := exists_div hΦ (e := 1 - e) (by linear_combination he) x0 fun Q hQ h => hQ (by
      have h5 := ev_add (Φ := Φ) (1 - e) e Q
      rw [sub_add_cancel, map_one, h1 Q ((hT Q).2 (hxQ Q h))] at h5
      exact left_eq_add.1 (h5.trans (add_comm _ _)))
    exact map_eq_one_of_sub _ (finSw D) _ hp hw
      ((resI_oToS l.Mb (half_ne_bot l) x).trans (Ideal.Quotient.eq_zero_iff_mem.2 hx))
  · obtain ⟨u, hu⟩ := hdiv d hd
    exact ⟨u, Subtype.ext (hu.trans hp.symm)⟩

theorem exists_unitary_part (V : HSp D) {e : AE D} (he : e * e = e) (he' : e * cA D e = 0) (hinf : infPart D e = 0)
    (m m' : Matrix (Fin V.rank) (Fin V.rank) (EAf D))
    (h : finSw D e • (m * m') = finSw D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D))) :
    ∃ g : GA D V, Formalism.L2.Theta.SuppAt e V g ∧ finSw D e • (finE V g).1 = finSw D e • m := by
  obtain ⟨M, M', hM, hMM⟩ := part_lift (swapAE D) (swp_bij (F := D.host.F) (E := D.host.E)) (finPart D e) m m' h
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hφ' : ∀ z, (φ z).1 = infPart D z ∧ (φ z).2 = finPart D z := hφ
  have hJK : JR (AF D.host.F) V.gram * (V.gram⁻¹).map (incA D) = 1 := by
    show V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.UnitaryGlue.gram_det_ne_zero V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (cA D) (JR (AF D.host.F) V.gram) = JR (AF D.host.F) V.gram := by
    refine Matrix.ext fun i j => ?_
    show cA D (incA D (V.gram j i)) = incA D (V.gram i j)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.SplitLift.exists_unitary_prod (infPart D) (finPart D) φ hφ' (cA D)
    GlobalTheory.DualPairCheck.cA_cA _ _ hJ hJK e he he' hinf M M' hMM
  refine ⟨⟨g, hg⟩, h1, ?_⟩
  rw [← hM]
  exact part_map (swapAE D) _ _ _ h2

theorem exists_stab_lift (l : Level H) {V : HSp D} {β : GL (Fin V.rank) (EAf D)}
    (hβ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts.IsLatBasis V rfl β) (Y₀ : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E))
    (hY₀ : IsUnit (Ideal.Quotient.mk l.Mb Y₀.det)) :
    ∃ κ ∈ GfC V, ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts.finR V rfl κ ∈ St β,
      (pullFr β ⟨_, h⟩).1.map (resI D.host.F l.Mb (half_ne_bot l)) = Y₀.map (Ideal.Quotient.mk l.Mb) := by
  have hB := GlobalTheory.GeoLevel.isBaseFrame_of_isLatBasis V β hβ
  obtain ⟨e, p, he, he', hinf, hp, hres, hdiv⟩ := exists_half_idem l
  have hpp : p * p = p := Subtype.ext (by
    show (p : EAf D) * p = p
    rw [hp, ← RingHom.map_mul, he])
  obtain ⟨u, hu⟩ := hdiv _ hY₀
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Y₀.map (oToS D.host.F D.host.E) := ⟨_, rfl⟩
  have hu' : u * Y.det = p := by
    rw [hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hu
  have hmm := conj_inv_part β p u Y hu' hpp
  rw [hp] at hmm
  obtain ⟨κ, hs, hκ⟩ := exists_unitary_part V he he' hinf _ _ hmm
  have hsf := supp_fin V (f := e + cA D e) hs
  rw [← hp] at hκ
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add, finSw_cA, hp]
  have hSt : finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram _ β hB.1 (hatL_selfDual hB) p u hpp (sigR_int p.2) Y hu' (finE V κ)
      (finE_mem_UA V κ) _ hf hsf hκ
  have hSt' : GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts.finR V rfl κ ∈ St β := by rw [GlobalTheory.GeoLevel.finR_rfl]; exact hSt
  refine ⟨κ, mem_GfC_of_suppF V (f := e + cA D e) ?_ hs, hSt', ?_⟩
  · rw [map_add, (parts_cA e).1, hinf, map_zero, add_zero]
  · have h1 := (Formalism.L2.DIV.frGL_pullFr β ⟨_, hSt'⟩).trans (GlobalTheory.GeoLevel.finR_rfl V κ)
    rw [← h1] at hκ
    rw [map_eq_of_smul_eq _ β _ p hres _ Y hκ, hY]
    exact Matrix.ext fun i j => resI_oToS l.Mb (half_ne_bot l) _

variable {Dw : Datum H}

theorem exists_isLevLift (l : Level H) (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι)
    (γ : GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.LevGrp Dw l) : ∃ κ, GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.IsLevLift l V ι γ κ := by
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_lattice_basis_hermitian_space D V _ rfl
  obtain ⟨φ, hφ⟩ := exists_coord l V rfl β hβ ι hι
  obtain ⟨Y, hY, hf⟩ := exists_matrix l.Mb (φ.symm.trans (LinearEquiv.trans γ φ))
  obtain ⟨κ, h1, h2, h3⟩ := exists_stab_lift l hβ Y hY
  refine ⟨κ, h1, (GlobalTheory.T.completedLattice_stabilizer_iff_basis_integral D V _ rfl β hβ κ).2 h2, (graph_iff φ _ _ (hφ κ h2) γ).1 fun q => ?_⟩
  rw [h3, ← hf, LinearEquiv.trans_apply, φ.symm_apply_apply]
  rfl

open GlobalTheory.UnifEvery in

theorem exists_isReduction : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (V : Formalism.BasicNotions.TH.HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (@HSpace.rank D.host.E _ _ D.host.cmStar V) → D.host.E)), LatEmb V ι → ∃ red : GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue.stabLat V →* GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelAut Dw l, GlobalTheory.LevDesc.IsReduction V ι red := by
  intro D H Dw l V ι hι
  have hs : ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue.stabLat V, (k : GA D V) ∈ GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1 := fun k =>
    mem_levSet_one.2 ⟨k.2.1, fun z hz => (k.2.2 z).2 hz⟩
  have hs' : ∀ {k : GA D V}, k ∈ GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1 → k ∈ GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue.stabLat V := fun {k} h =>
    ⟨h.1, fun z => ⟨fun hz => by
      have := GlobalTheory.RecDict.finHom_inv_mulVec_mem V k (mem_levSet_one.1 h).2 _ hz
      rwa [← finHom_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec] at this,
      (mem_levSet_one.1 h).2 z⟩⟩
  choose r hr using fun k : GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue.stabLat V => GlobalTheory.T.exists_lattice_automorphism_mod_halfLevel D V H Dw l ι hι k (hs k)
  have hi : ∀ k, Ind V l ι (r k) k := fun k => ⟨hs k, hr k⟩
  obtain ⟨Kf, hK, -⟩ := GlobalTheory.RecDict.exists_isLevelK D V l.M
  have hone := ind_one_iff hι hK ((GlobalTheory.Member.finCong_iff_half_and_kfHalf D H l V).2 Kf hK)
  refine ⟨MonoidHom.mk' r fun a b => (hi (a * b)).unique hι ((hi a).mul hι (hi b)), fun γ => ?_, fun k => ⟨fun h => ?_,
    fun h => ?_⟩, fun k a ha => ?_⟩
  · obtain ⟨κ, hκ⟩ := exists_isLevLift l V ι hι γ
    have h := ind_of_isLevLift hι hκ
    exact ⟨⟨κ, hs' h.1⟩, (hi _).unique hι h⟩
  · have h1 : r k = 1 := h
    exact ⟨k.2, ((hone k).1 (h1 ▸ hi k)).2⟩
  · exact (hi k).unique hι ((hone k).2 ⟨k.2.1, h.2⟩)
  · obtain ⟨w, hw, e⟩ := ((hi k).isLevLift hι).2.2 a ha _ (map_mem_smul_top (liftLa (r k)) ha) (liftLa_spec _ a)
    exact ⟨-w, neg_mem hw, by rw [neg_nsmul, ← e, neg_sub]; rfl⟩

end GlobalTheory.LevelReduction
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelIsometry

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp GlobalTheory.DictMove GlobalTheory.AllWt GlobalTheory.LevDesc GlobalTheory.LevelKeeps
open GlobalTheory.Dict (castFr)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.FormTies (levFull)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem val_transl_nonneg (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (γ : LevelAut Dw l) {e : Ix Dw → ℤ}
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (h : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) :
    ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v (transl Xo c γ f) := by
  rintro la _ ⟨⟨q, S, io, n, ho, y, hy, η, hη, rfl⟩, rfl⟩
  let := io.toAlgebra
  have hmv := levR_move hpq hA γ y.1
  let y' : IntFr Xo c S io :=
    ⟨_, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      GlobalTheory.FormTies.LevelMove.integral_of_levR _ _ _ _ _ _ (levFull Dw l γ) S io y.1 _ hmv y.2.2⟩
  have h0 : 0 ≤ nval S.V n (evI y' f) := h la _ ⟨PtV.mk la ho y' hy () trivial, rfl⟩
  have e1 : evI y (transl Xo c γ f) = evI y' f := evR_transl hpq hA γ hf y.1
  show 0 ≤ nval S.V n (evI y (transl Xo c γ f))
  rw [e1]
  exact h0

variable {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ}

theorem norm_rdU_transl (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hP : HasPeriods φ)
    (hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0) (γ : LevelAut Dw l) {k k' : U.Comp} {δ : GL (Fin r) E}
    (h : Carries φ (levFull Dw l γ).1 k k' δ) {w : Ix Dw → ℤ} (hw : Even (w none)) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c w) {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    ‖rdU U (transl Xo c γ f) k x‖ = ‖rdU U f k' (lact δ (castFr h.mt.psi x))‖ := by
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hA' : l.A.Coprime l.M := by rw [hA]; exact Nat.coprime_one_left _
  obtain ⟨z, hz1, hz⟩ := exists_const_of_carries (w := 0) (n := 2) (s' := (levFull Dw l γ).2) hσ hU hpq hA hP hxi
    ⟨fun _ => antitone_const, even_two⟩ (transl Xo c γ)
    (fun f hf => by rw [← secZ_nat] at hf ⊢; exact transl_mem_secZ hpq hA' γ hf)
    (fun y => by
      obtain ⟨ρ, ν, -, hν, hm⟩ := levR_move hpq hA' γ y
      exact ⟨ρ, ν, _, hν, hm, fun f hf => by rw [← secZ_nat] at hf; exact evR_transl hpq hA' γ hf y⟩) h
  obtain ⟨m, hm⟩ := hw
  obtain ⟨ρ, ν, -, hν, hmv⟩ := levR_move hpq hA' γ (U.un k ⟨x, hx⟩)
  obtain ⟨a₁, b₁⟩ := move_eq hσ hpq hA hP h hν ⟨x, hx⟩ hmv
  obtain ⟨t₀, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen _ _ a₁ b₁
  have key : ∀ (w : Ix Dw → ℤ), ∀ f ∈ secZ Xo c w, rdU U (transl Xo c γ f) k x =
      toC (t₀ : CAt σ) ^ w none * rdU U f k' (lact δ (castFr h.mt.psi x)) := fun w f hf => by
    have v1 : rdU U (transl Xo c γ f) k x = toC (evR Xo c (transl Xo c γ f) (U.un k ⟨x, hx⟩)) := dif_pos hx
    have v2 : rdU U f k' (lact δ (castFr h.mt.psi x)) = toC (evR Xo c f (U.un k' ⟨_, h.mt.mem_dom hx⟩)) :=
      dif_pos (h.mt.mem_dom hx)
    rw [v1, v2, evR_transl hpq hA' γ hf, GlobalTheory.FlagTan.evR_frBor hf ht, Fintype.prod_option]
    simp only [Option.elim, one_zpow, Finset.prod_const_one, mul_one]
    exact congrArg (· * toC (evR Xo c f (U.un k' ⟨_, h.mt.mem_dom hx⟩))) (Units.val_zpow_eq_zpow_val (α := ℂ) t₀ _)
  obtain ⟨f₂, hf₂, h0⟩ := exists_sec_two hσ hU (hU.1 ▸ hpq) k' (h.mt.mem_dom hx)
  have h2 := hz f₂ hf₂ x hx
  rw [← secZ_nat] at hf₂
  rw [key _ f₂ hf₂] at h2
  have h3 : toC (t₀ : CAt σ) ^ (2 : ℤ) = z := mul_right_cancel₀ h0 h2
  rw [key w f hf, hm, ← two_mul, zpow_mul, h3, norm_mul, norm_zpow, hz1, one_zpow, one_mul]

end Free

section Adelic

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.LevDesc GlobalTheory.DictMove
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.FormTies (levFull)
open scoped Matrix TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def rightEquiv (V : HSp D) (κ : GA D V) : AutQ V ≃ᵐ AutQ V :=
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have hrel : ∀ (k a b : GA D V), QuotientGroup.rightRel (GQ V) a b → QuotientGroup.rightRel (GQ V) (a * k) (b * k) :=
    fun k a b h => by
      rw [QuotientGroup.rightRel_apply] at h ⊢
      rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  have hm : ∀ k : GA D V, Measurable (Quotient.map' (· * k) (hrel k) : AutQ V → AutQ V) := fun k _ hs =>
    measurable_mul_const k (autMk_measurable V hs)
  { toFun := Quotient.map' (· * κ) (hrel κ)
    invFun := Quotient.map' (· * κ⁻¹) (hrel κ⁻¹)
    left_inv := fun q => Quotient.inductionOn q fun a => congrArg (autMk V) (mul_inv_cancel_right a κ)
    right_inv := fun q => Quotient.inductionOn q fun a => congrArg (autMk V) (inv_mul_cancel_right a κ)
    measurable_toFun := hm κ
    measurable_invFun := hm κ⁻¹ }

theorem eLpNorm_right (V : HSp D) (hs : V.SigOK) (κ : GA D V) (Φ : GA D V → ℝ)
    (hΦ : ∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) (p : ENNReal) :
    eLpNorm (fun q : AutQ V => Φ (q.out * κ)) p (muQ1 V) = eLpNorm (fun q : AutQ V => Φ q.out) p (muQ1 V) := by
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hR := ((GlobalTheory.CoreLawsCompare.invProb_iff V hP hV _).2 rfl).2
  have hmap : (muQ1 V).map (rightEquiv V κ) = muQ1 V := Measure.ext fun s hs => by
    rw [MeasurableEquiv.map_apply]
    exact hR κ _ (fun _ => rfl) s hs
  have hout : ∀ g, Φ (autMk V g).out = Φ g := fun g => by
    have e : (QuotientGroup.rightRel (GQ V)) g (autMk V g).out := Quotient.exact (Quotient.out_eq (autMk V g)).symm
    rw [QuotientGroup.rightRel_apply] at e
    rw [← hΦ _ e g, inv_mul_cancel_right]
  conv_rhs => rw [← hmap, (rightEquiv V κ).measurableEmbedding.eLpNorm_map_measure]
  congr 1
  funext q
  rw [← hout (q.out * κ)]
  exact congrArg (fun q' : AutQ V => Φ (rightEquiv V κ q').out) (Quotient.out_eq q)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem exists_induces (V : HSp D) {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι)
    (γ : LevelAut Dw l) : ∃ κ, Induces V l ι (levFull Dw l γ).1 κ := by
  obtain ⟨red, h1, -, h3⟩ := GlobalTheory.LevelReduction.exists_isReduction D H Dw l V ι hι
  obtain ⟨k, rfl⟩ := h1 γ
  refine ⟨k, k.2.1, ?_, fun a ha => ?_⟩
  · have e : Formalism.L2.Pj.gLat V k = Formalism.L2.Pj.gLat V 1 := by
      unfold Formalism.L2.Pj.gLat
      rw [map_one, Units.val_one]
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨_, (k.2.2 y).2 hy, Matrix.one_mulVec _⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨_, ((k⁻¹).2.2 y).2 hy, ?_⟩
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          map_one, Units.val_one]
    unfold latGHat
    rw [e]
  · obtain ⟨w, hw, e⟩ := h3 k a ha
    exact ⟨-w, neg_mem hw, by rw [neg_nsmul, ← e, neg_sub]; exact (add_sub_cancel _ _).symm⟩

set_option maxHeartbeats 1000000 in

theorem petE_transl {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {V : HSp D}
    (hs : V.SigOK) (hr : V.rank = r) {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} {g : ℕ}
    {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th th' : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {Kf : Subgroup (GA D V)}
    (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hW : ∀ k, ModelW V hr (U.X k))
    (hι : LatEmb V ι) (hL : DictLat U V hr dict ι e F ik φ th x₀) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hD : DictIsUnif V dict Kf th' hr) (hu : ∀ g τ i, ‖dmin (U.X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    {G : WTZ D.host.E} (hG : Even G.2) (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (modelWt U G k) γ = 1)
    (γ : LevelAut Dw l) {f : Rul Xo c} (hf : f ∈ secZ Xo c (exZ Dw G)) (hfc : rdU U f ∈ holSub U.X (modelWt U G)) :
    petE V dict (muQ1 V) (modelWt U G) (rdU U (transl Xo c γ f)) = petE V dict (muQ1 V) (modelWt U G) (rdU U f) := by
  subst hr
  obtain ⟨κ, hκ⟩ := exists_induces V hι γ
  have hN : ∀ (P : FDSec U.X) g, ptN (modelWt U G) P (dict g) = ‖P (dict g).1 (dict g).2‖ := fun P g =>
    pnorm_eq_of_unit _ _ _ _ (hu g)
  unfold petE
  simp only [hN]
  rw [← eLpNorm_right V hs κ (fun g => ‖rdU U f (dict g).1 (dict g).2‖) fun a ha h => by
    obtain ⟨a', ha', e₁⟩ := hD.1 a ha h
    have := (GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ hfc (dict h).1).1.1.2.2 a' ha' _ (hD.2.2.2.1 h)
    rw [hχ _ _ ha', one_mul] at this
    rw [e₁]
    exact congrArg norm this]
  congr 1
  funext q
  obtain ⟨hx, δ, hc, e₁⟩ := GlobalTheory.StabMove.exists_carries (V := V) (W := V) rfl rfl rfl (dict := dict) ι hU hW hL hth
    hD.2.2.2.1 hκ q.out
  change (dict (q.out * κ)).2 = _ at e₁
  rw [e₁]
  exact norm_rdU_transl hσ hU hpq hA hL.1.2 (fun k k' => (hW k).2.trans (hW k').2.symm) γ hc hG hf hx

end Adelic

end GlobalTheory.LevelIsometry

end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.LevDesc (transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open scoped TensorProduct
open GlobalTheory GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ G : WTZ D.host.E, Even G.2 → KeepsCusp Y.U G ∧ ∀ (γ : LevelAut (T.Q.Dw j) Y.d.l₂) (f g : Y.V G), (g : Rul Y.d.Xo₂ Y.d.c₂) = pull Y.d.Xo₂ Y.d.c₂ γ f → (f ∈ AllWt.latW Y.U G → g ∈ AllWt.latW Y.U G) ∧ ∀ σ, Y.nrm G σ g = Y.nrm G σ f := by
  intro D T hT j hp _ _ hj Y e o hY G hG
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := le_add_right hp
  have hA := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := by rw [hA]; exact Nat.coprime_one_left _
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hT.pins.2.1.1]
  have hχ := fun σ hσ => GlobalTheory.AllWt.Model.chi_modelWt (Y.U σ) (hY.chiTriv σ hσ) G hG
  obtain ⟨ι, hι, -, hpin⟩ := hY.adPin
  refine ⟨GlobalTheory.LevelKeeps.keepsCusp_of_isUnf hpq hA hG hY.unf (fun σ hσ k k' => ?_) (fun σ hσ => ?_) hχ,
    fun γ f g hg => ⟨fun hf => ?_, fun σ => ?_⟩⟩
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    exact ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    obtain ⟨th, _, hth, hD⟩ := hY.dictU σ hσ
    obtain ⟨x₀, h0, _, g, e, F, ik, φ, th', hth', hL⟩ := hpin σ hσ
    obtain rfl : th = th' := funext fun k => funext fun τ =>
      GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth k τ) (hth' k τ)
    exact GlobalTheory.LevelKeeps.mem_group (hY.unf σ hσ) hA ((hY.unf σ hσ).1 ▸ hpq) hr hW h0 (hM ▸ hY.levelK) hth hD fun h => by
      obtain ⟨γ, -, -, -, h3⟩ := hL.2 h
      exact ⟨_, h3⟩
  · intro la v hv
    show 0 ≤ v (g : Rul Y.d.Xo₂ Y.d.c₂)
    rw [hg]
    exact GlobalTheory.LevelIsometry.val_transl_nonneg hpq hA' γ⁻¹ (AllWt.mem_cuspW.1 f.2).1 hf la v hv
  · have hσ := goodEmb_goodOf (c := Y.d.c₂) σ
    obtain ⟨hr, hW⟩ := hY.modelW _ hσ
    obtain ⟨th, _, -, hD⟩ := hY.dictU _ hσ
    obtain ⟨x₀, -, _, g', e, F, ik, φ, th', hth', hL⟩ := hpin _ hσ
    have := GlobalTheory.LevelIsometry.petE_transl (D.sp.W_sig j) hr hσ (hY.unf _ hσ) hpq hA hW hι hL hth' hD (hY.unit _ hσ) hG
      (hχ _ hσ) γ⁻¹ (AllWt.mem_cuspW.1 f.2).1 ((AllWt.mem_cuspW.1 f.2).2 _ hσ)
    show _ * (AllWt.petE _ _ _ _ (rdU _ (g : Rul Y.d.Xo₂ Y.d.c₂))).toReal = _
    rw [hg]
    exact congrArg (fun t : ENNReal => AllWt.lieFacZ (T.Q.Dw j) (xiR D) G * t.toReal) this
end
