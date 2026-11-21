import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowAsm
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Mathlib
import Formalism.LocalRingCardinality.DataIdx
import Formalism.LocalRingCardinality.DataNChTie
import Formalism.SharpRestriction.InertJacobiLevels.ResCharConj
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowD
import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevM

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open scoped TensorProduct nonZeroDivisors

section Kap

variable (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [Algebra.IsIntegral A B]

theorem isFrac_tensor (hinj : Function.Injective (algebraMap A B)) :
    IsFractionRing B (B ⊗[A] FractionRing A) := by
  have h0 : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (B ⊗[A] FractionRing A) := inferInstance
  refine IsLocalization.of_le (Algebra.algebraMapSubmonoid B A⁰) B⁰ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha))
  · intro r hr
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := A) (I := Ideal.span {r}) hr0
      (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
    obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hd)
    have hu : IsUnit (algebraMap B (B ⊗[A] FractionRing A) (algebraMap A B d)) :=
      IsLocalization.map_units (M := Algebra.algebraMapSubmonoid B A⁰) _
        ⟨_, ⟨d, mem_nonZeroDivisors_of_ne_zero hd0, rfl⟩⟩
    rw [hs, map_mul] at hu
    exact isUnit_of_mul_isUnit_left hu

def kap (hinj : Function.Injective (algebraMap A B)) : (B ⊗[A] FractionRing A) ≃ₐ[B] FractionRing B :=
  haveI := isFrac_tensor A B hinj
  IsLocalization.algEquiv B⁰ _ _

variable (ι : Type) [Fintype ι] [DecidableEq ι]

def vecE (hinj : Function.Injective (algebraMap A B)) :
    (ι → FractionRing B) ≃ₗ[B] B ⊗[A] (ι → FractionRing A) :=
  (LinearEquiv.piCongrRight fun _ : ι => (kap A B hinj).symm.toLinearEquiv) ≪≫ₗ
    (TensorProduct.piRight A B B (fun _ : ι => FractionRing A)).symm


theorem single_li (hB : Function.Injective (algebraMap B (FractionRing B))) :
    LinearIndependent B (fun a : ι => (Pi.single a 1 : ι → FractionRing B)) := by
  have h := (Pi.basisFun (FractionRing B) ι).linearIndependent
  have h2 := h.restrict_scalars (R := B) (by
    intro x y hxy
    simpa [Algebra.smul_def] using hB (by simpa [Algebra.smul_def] using hxy))
  have e : (fun a : ι => (Pi.single a 1 : ι → FractionRing B)) = ⇑(Pi.basisFun (FractionRing B) ι) :=
    funext fun a => (Pi.basisFun_apply _ _ a).symm
  rw [e]; exact h2

end Kap

theorem basis_of_basisF {K F W M ι κ : Type} [Field K] [Field F] [AddCommGroup W] [Module K W] [AddCommGroup M]
    [Module F M] [Fintype ι] [Fintype κ] (σ : K →+* F) (e : W →ₛₗ[σ] M)
    (b : Module.Basis ι K W)
    (hb : LinearIndependent F (fun i => e (b i)) ∧ Submodule.span F (Set.range fun i => e (b i)) = ⊤)
    (b' : Module.Basis κ K W) :
    LinearIndependent F (fun i => e (b' i)) ∧ Submodule.span F (Set.range fun i => e (b' i)) = ⊤ := by
  have hexp' : ∀ x : W, e x = ∑ i, σ (b'.repr x i) • e (b' i) := fun x => by
    conv_lhs => rw [← b'.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ e _ _
  have hspan : Submodule.span F (Set.range fun i => e (b' i)) = ⊤ := by
    rw [eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show e (b i) ∈ _
    rw [hexp' (b i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨?_, hspan⟩
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b', ← Module.finrank_eq_card_basis b]
  let B : Module.Basis ι F M := Module.Basis.mk hb.1 hb.2.ge
  have hfin : Module.finrank F M = Fintype.card κ := by
    rw [Module.finrank_eq_card_basis B, hcard]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hfin.symm

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

def scalAct {Γ : Type} [Group Γ] (K V : Type) [Field K] [AddCommGroup V] [Module K V] (ψ : Γ →* Kˣ) :
    Γ →* (V ≃ₗ[K] V) := (DistribMulAction.toModuleAut K V).comp ψ

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂}

set_option synthInstance.maxHeartbeats 400000 in

structure NzIn (C : TwCore R H what₂ LL0 N) : Type 1 where
  eA : ∀ i, Bool → MonoidAlgebra (FractionRing (C.O i)) (G0g N)
  eL : G0g N → LL0
  eA_def : ∀ i b (g : G0g N), (eA i b).coeff g =
    IsFractionRing.map (A := C.O0 i) (B := C.O i) (K := FractionRing (C.O0 i))
      (L := FractionRing (C.O i)) (C.O_inj i) ((if b then C.emb0 i else C.emb0b i) (eL g))
  eA_idem : ∀ i b, eA i b * eA i b = eA i b
  eA_central : ∀ i b x, eA i b * x = x * eA i b
  Psi : ∀ i, G0g N →* (FractionRing (C.O i))ˣ
  hPsi : ∀ i b (V : Type) [AddCommGroup V] [Module (FractionRing (C.O i)) V],
    MonoidAlgebra.lift (FractionRing (C.O i)) (Module.End (FractionRing (C.O i)) V) (G0g N)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (scalAct _ V (Psi i))) (eA i b) = 1
  ix : ℕ → Type
  [ixF : ∀ j, Fintype (ix j)]
  [ixD : ∀ j, DecidableEq (ix j)]
  ix_out : ∀ j, Nonempty (ix j) → 1 ≤ j ∧ j ≤ R.m
  ixM : ℕ → Type
  [ixMF : ∀ j, Fintype (ixM j)]
  [ixMD : ∀ j, DecidableEq (ixM j)]
  rM : ∀ j, ix j → ixM j

attribute [instance] NzIn.ixF NzIn.ixD NzIn.ixMF NzIn.ixMD

namespace TwCore

variable (C : TwCore R H what₂ LL0 N) (I : NzIn C)

def SigN : Type := {p : Fin (R.m + 1) × Bool // 1 ≤ p.1.1 ∧ Nonempty (I.ix p.1.1)}

instance : Finite (SigN C I) := inferInstanceAs (Finite {p : Fin (R.m + 1) × Bool // _})



open Classical in
set_option synthInstance.maxHeartbeats 400000 in

abbrev toTwN [hL : IsEmpty N.Loc] : NTw R H what₂ LL0 N where
  cc := C.cc
  cc_cm := C.cc_cm
  Tw := C.Tw
  l := C.l
  lPrime := C.lPrime
  O0 := C.O0
  crO0 := C.crO0
  twistBaseCoefficientRing_isDomain := C.twistBaseCoefficientRing_isDomain
  twistBaseCoefficientRing_isDVR := C.twistBaseCoefficientRing_isDVR
  algO0 := C.algO0
  twistBaseCoefficientRing_finite_padic := C.twistBaseCoefficientRing_finite_padic
  twistBaseCoefficientRing_residueField_finite := C.twistBaseCoefficientRing_residueField_finite
  topO0 := C.topO0
  twistBaseCoefficientRing_topologicalRing := C.twistBaseCoefficientRing_topologicalRing
  twistBaseCoefficientRing_isAdic := C.twistBaseCoefficientRing_isAdic
  emb0 := C.emb0
  emb0b := C.emb0b
  restX_coefficientEmbedding_conj := C.restX_coefficientEmbedding_conj
  O := C.O
  crO := C.crO
  domO := C.domO
  dvrO := C.dvrO
  algO := C.algO
  O_inj := C.O_inj
  O_l := C.O_l
  topO := C.topO
  trO := C.trO
  O_adic := C.O_adic
  resO_ac := C.resO_ac
  O_complete := C.O_complete
  Ok := C.Ok
  crOk := C.crOk
  domOk := C.domOk
  dvrOk := C.dvrOk
  algOk := C.algOk
  Ok_inj := C.Ok_inj
  Ok_fin := C.Ok_fin
  zk := C.zk
  zk_prim := C.zk_prim
  Ok_gen := C.Ok_gen
  pD := C.pD
  pD_eq := C.pD_eq
  delta := C.delta
  delta_open := C.delta_open
  delta_anti := C.delta_anti
  delta_ram := C.delta_ram
  delta_15 := C.delta_15
  delta_tame := C.delta_tame
  RCG := C.RCG
  grpRCG := C.grpRCG
  finRCG := C.finRCG
  RCG_l := C.RCG_l
  art := C.art
  art_surj := C.art_surj
  art_cont := C.art_cont
  art_anti := C.art_anti
  art_unr := C.art_unr
  art_univ := C.art_univ
  res := C.res
  res_art := C.res_art
  chi1 i _ b := C.chi i b
  twistCharacterFamily_continuous i _ b := C.chi_cont i b
  twistCharacterFamily_unramified i _ b v _ _ hv A hA σ hσ := by rw [chi_apply, C.delta_unr i v hv A hA σ hσ]; simp
  twistCharacterFamily_at_auxiliaryPlaces i _ b _ _ _ _ σ _ := C.chi_apply i b σ
  twistCharacterFamily_tame i _ b k v hv _ A hA σ hσ := by
    rw [chi_apply, C.delta_unr i v (C.g_not_pD i k v hv) A hA σ hσ]; simp
  Sig _ := SigN C I
  finSig _ := Fintype.ofFinite _
  jS _ s := s.1.1.1
  jS_range _ s := ⟨s.2.1, Nat.lt_succ_iff.mp s.1.1.2⟩
  side _ s := s.1.2
  rhoS _ _ := 1
  rhoS_cont _ _ := continuous_const
  hEig _ _ _ _ := 1
  S0 i := (placesOver_finite H.E (C.l i) (C.lPrime i).out.ne_zero).toFinset ∪
    (placesOver_finite H.E (H.g 0) (H.g_prime 0).ne_zero).toFinset ∪
    (placesOver_finite H.E (H.g 1) (H.g_prime 1).ne_zero).toFinset ∪ C.pD i
  twistExcludedPlaces_contains_residueChar i v hv := by simp [hv]
  placesOver_subset_exceptional i k v hv := by fin_cases k <;> simp_all
  primes_subset_exceptional i := Finset.subset_union_right
  B i j _ := I.ix j → C.O i
  Theta _ _ _ := ⊤
  ThetaPsi _ _ _ _ _ _ := ⊤
  ThetaPsi_one _ _ _ _ := (Submodule.baseChange_top _).symm
  hk _ _ _ _ _ := 1
  hk_zero _ _ _ _ := rfl
  abelian₂ _ := Empty
  jL _ s := s.elim
  sideL _ s := s.elim
  s2 _ s := s.elim
  jL_range _ s := s.elim
  lamG _ s := s.elim
  lamG_cont _ s := s.elim
  lamG_unr _ s := s.elim
  lamG_pD _ s := s.elim
  lamG_anti _ s := s.elim
  Xv _ s := s.elim
  Xv_def _ s := s.elim
  qs _ s := s.elim
  qs_sq _ s := s.elim
  qs_conj _ s := s.elim
  th _ _ s := s.elim
  twOf a := hL.elim a
  twSide a := hL.elim a
  twOf_l a := hL.elim a
  twist₂ a := hL.elim a
  twO_emb a := hL.elim a
  psiL a := hL.elim a
  psiL_ord a := hL.elim a
  psiL_open a := hL.elim a
  psiL_anti a := hL.elim a
  psiL_ram a := hL.elim a
  psiL_l a := hL.elim a
  chi_tw a := hL.elim a

variable [hL : IsEmpty N.Loc]

def incl (A K : Type) [CommRing A] [CommRing K] [Algebra A K] (ι : Type) : (ι → A) →ₗ[A] (ι → K) :=
  (Algebra.linearMap A K).compLeft ι

theorem mem_range_incl {A K : Type} [CommRing A] [CommRing K] [Algebra A K] {ι : Type} (f : ι → K) :
    f ∈ LinearMap.range (incl A K ι) ↔ ∀ y, f y ∈ (algebraMap A K).range := by
  constructor
  · rintro ⟨g, rfl⟩ y
    exact ⟨g y, rfl⟩
  · intro h
    choose g hg using h
    exact ⟨g, funext hg⟩

theorem single_mem_incl {A K : Type} [CommRing A] [CommRing K] [Algebra A K] {ι : Type} [DecidableEq ι] (a : ι) :
    (Pi.single a 1 : ι → K) ∈ LinearMap.range (incl A K ι) :=
  ⟨Pi.single a 1, funext fun y => by
    show algebraMap A K ((Pi.single a 1 : ι → A) y) = _
    by_cases h : y = a
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]⟩

theorem range_incl_eq_span (A K : Type) [CommRing A] [CommRing K] [Algebra A K] (ι : Type) [Fintype ι] [DecidableEq ι] :
    LinearMap.range (incl A K ι) = Submodule.span A (Set.range fun a : ι => (Pi.single a 1 : ι → K)) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    have e : incl A K ι g = ∑ a, g a • (Pi.single a 1 : ι → K) := by
      funext y
      rw [Finset.sum_apply, Finset.sum_eq_single y]
      · show algebraMap A K (g y) = g y • (Pi.single y 1 : ι → K) y
        rw [Pi.single_eq_same, Algebra.smul_def, mul_one]
      · intro b _ hb
        show g b • (Pi.single b 1 : ι → K) y = 0
        rw [Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
      · intro h; exact absurd (Finset.mem_univ y) h
    rw [e]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact single_mem_incl a

theorem span_incl_top (A K : Type) [CommRing A] [Field K] [Algebra A K] (ι : Type) [Fintype ι] [DecidableEq ι] :
    Submodule.span K (LinearMap.range (incl A K ι) : Set (ι → K)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K ι).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  rw [Pi.basisFun_apply]
  exact single_mem_incl a

instance (i k) : Algebra.IsIntegral (C.O i) (C.Ok i k) :=
  haveI := C.Ok_fin i k
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in

abbrev toExpN : NExp R H what₂ LL0 N (C.toTwN I) where
  Fm (i : C.Tw) j _ := I.ix j → FractionRing (C.O i)
  actG (i : C.Tw) j _ := scalAct _ _ (I.Psi i)
  U := ⊥
  psiU _ _ := 1
  eAlg := I.eA
  eLL0 := I.eL
  eAlg_def := I.eA_def
  eAlg_idem := I.eA_idem
  eAlg_central := I.eA_central
  Bsup (i : C.Tw) j _ := LinearMap.range (incl (C.O i) (FractionRing (C.O i)) (I.ix j))
  Dat _ j _ := I.ix j
  th (i : C.Tw) j _ (d : I.ix j) := (Pi.single d 1 : I.ix j → FractionRing (C.O i))
  lev _ _ _ _ := ∅
  thPsi (i : C.Tw) j _ k _ _ (d : I.ix j) := {(1 : C.Ok i k) ⊗ₜ[C.O i] (Pi.single d 1 : I.ix j → FractionRing (C.O i))}
  thPsi_one _ _ _ _ _ := rfl
  thU (i : C.Tw) j _ _ _ (d : I.ix j) := (Pi.single d 1 : I.ix j → FractionRing (C.O i)) ⊗ₜ[C.O i] 1
  twPsi (i : C.Tw) j _ k _ := TensorProduct.mk (C.O i) (C.Ok i k) (I.ix j → FractionRing (C.O i)) 1
  twPsi_one _ _ _ _ _ := rfl
  twDel (i : C.Tw) j _ _ _ := (TensorProduct.mk (C.O i) (I.ix j → FractionRing (C.O i)) _).flip 1
  delU _ _ _ := 1
  delU_unr := by intros; rfl
  delU_l := by intros; rfl
  delU_anti _ _ _ _ _ _ := by simp
  delU_open _ _ _ := by simp [MonoidHom.ker_one]
  delU_res := by intros; rfl
  delU_conj _ _ _ _ _ _ _ _ := ⟨1, fun _ => by simp⟩
  MtV (i : C.Tw) j _ k _ _ := I.ixM j → FractionRing (C.Ok i k)
  MtLat (i : C.Tw) j _ k _ _ := LinearMap.range (incl (C.Ok i k) (FractionRing (C.Ok i k)) (I.ixM j))
  MtLat_fg (i : C.Tw) j _ k _ _ := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  MtLat_span (i : C.Tw) j _ k _ _ := span_incl_top _ _ _
  thP (i : C.Tw) j _ k _ _ := (NZ.vecE (C.O i) (C.Ok i k) (I.ix j) (C.Ok_inj i k)).toLinearMap ∘ₗ
    LinearMap.funLeft (C.Ok i k) (FractionRing (C.Ok i k)) (I.rM j)
  hkF _ _ _ _ _ := 1
  embB (i : C.Tw) j _ := incl (C.O i) (FractionRing (C.O i)) (I.ix j)
  embB_inj (i : C.Tw) j _ (x y : I.ix j → C.O i) h := funext fun a => IsFractionRing.injective (C.O i) (FractionRing (C.O i)) (congrFun h a)
  eH _ _ _ := 1
  eH_idem _ _ _ := mul_one _

open Classical in
set_option synthInstance.maxHeartbeats 400000 in

def toThN : NTh R H what₂ LL0 N (C.toTwN I) (C.toExpN I) where
  iC := C.iC
  iC_int := C.iC_int
  aL (i : C.Tw) := if ∃ k, C.l i = H.g k then 1 else 0
  aL_g (i : C.Tw) k h := if_pos ⟨k, h⟩
  aL_off (i : C.Tw) h := if_neg fun ⟨k, hk⟩ => h k hk
  Pt _ j := I.ix j
  ev (i : C.Tw) j _ :=
    { toFun := fun (f : I.ix j → FractionRing (C.O i)) y => C.iC i (f y)
      map_zero' := funext fun _ => map_zero _
      map_add' := fun (f g : I.ix j → FractionRing (C.O i)) => funext fun _ => map_add _ _ _ }
  ev_smul (i : C.Tw) j _ a (f : I.ix j → FractionRing (C.O i)) y := map_mul (C.iC i) a (f y)
  ev_inj (i : C.Tw) j _ (f g : I.ix j → FractionRing (C.O i)) h := funext fun y => (C.iC i).injective (congrFun h y)
  Lt _ j := I.ix j → 𝓞 H.E
  Let _ _ := Empty
  Harm _ _ := Set.univ
  Ctr _ _ := Empty
  ctrC _ _ κ := κ.elim
  Harm_def _ _ _ := ⟨fun _ κ => κ.elim, fun _ => trivial⟩
  thV (i : C.Tw) j (φ : (I.ix j → 𝓞 H.E) → FractionRing (C.O i)) (P : MvPolynomial Empty (C.O i)) (y : I.ix j) :=
    C.iC i (φ (Pi.single y 1)) *
    C.iC i (algebraMap (C.O i) (FractionRing (C.O i)) (MvPolynomial.constantCoeff P))
  thV_add (i : C.Tw) j (φ φ' : (I.ix j → 𝓞 H.E) → FractionRing (C.O i)) P y := by
    show C.iC i (φ _ + φ' _) * _ = _
    rw [map_add, add_mul]
  thV_smul (i : C.Tw) j a (φ : (I.ix j → 𝓞 H.E) → FractionRing (C.O i)) P y := by
    show C.iC i (a * φ _) * _ = _
    rw [map_mul, mul_assoc]
  thV_addP (i : C.Tw) j φ (P P' : MvPolynomial Empty (C.O i)) y := by
    show _ * C.iC i (algebraMap _ _ (MvPolynomial.constantCoeff (P + P'))) = _
    rw [map_add, map_add, map_add, mul_add]
  thV_smulP (i : C.Tw) j (c : C.O i) φ (P : MvPolynomial Empty (C.O i)) y := by
    show _ * C.iC i (algebraMap _ _ (MvPolynomial.constantCoeff (c • P))) = _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.constantCoeff_C, map_mul, map_mul]
    ring
  datPhi (i : C.Tw) j _ (d : I.ix j) (z : I.ix j → 𝓞 H.E) := if z = Pi.single d 1 then (1 : FractionRing (C.O i)) else 0
  datP _ _ _ _ := 1
  recDet _ _ _ := 1
  Kq _ _ _ := PUnit
  actK _ _ _ _ y := y
  actK_one _ _ _ _ := rfl
  actK_mul _ _ _ _ _ _ := rfl
  recDetq _ _ _ _ := 1
  recDetq_mem _ _ _ _ := one_mem _
  recDet_act := by intros; rfl
  recDetq_act := by intros; rfl
  hkIdx _ _ _ _ := Unit
  hkMove _ _ _ _ _ y := y
  hkU _ _ _ _ _ _ _ := 1
  hk_ev (i : C.Tw) j b k P _ _ _ _ (f : I.ix j → FractionRing (C.O i)) y := by
    rw [Finset.univ_unique, Finset.sum_singleton, one_mul]
    rfl
  MaximalUnramifiedExtension _ := ⊤
  FmUr _ _ _ := ⊤
  FmUr_smul := by intros; trivial
  FmUr_span _ _ _ := eq_top_iff.mpr fun x _ => Submodule.subset_span trivial
  Bsup_def (i : C.Tw) j _ := by
    have e : {f : I.ix j → FractionRing (C.O i) | f ∈ (⊤ : AddSubgroup _) ∧ ∀ y, ‖C.iC i (f y)‖ ≤ 1} =
        (LinearMap.range (incl (C.O i) (FractionRing (C.O i)) (I.ix j)) : Set _) := by
      ext f
      simp only [Set.mem_setOf_eq, AddSubgroup.mem_top, true_and, SetLike.mem_coe, mem_range_incl, C.iC_int]
    exact (Submodule.span_eq _).symm.trans (congrArg _ e.symm)

end TwCore

end Formalism.BasicNotions.Examples₂
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

section Coord

variable {K F W ι : Type} [Field K] [Field F] [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι]
  (σ : K →+* F) (b : Module.Basis ι K W)

def coordMap : W →ₛₗ[σ] (ι → F) where
  toFun x a := σ (b.repr x a)
  map_add' x y := funext fun a => by simp
  map_smul' c x := funext fun a => by simp

theorem coordMap_apply (x : W) (a : ι) : coordMap σ b x a = σ (b.repr x a) := rfl

theorem coordMap_basis (i : ι) : coordMap σ b (b i) = Pi.single i 1 := by
  funext a
  rw [coordMap_apply, b.repr_self, Finsupp.single_apply, Pi.single_apply]
  split_ifs with h1 h2 h2
  · exact map_one σ
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact map_zero σ

theorem coordMap_good : LinearIndependent F (fun i => coordMap σ b (b i)) ∧
    Submodule.span F (Set.range fun i => coordMap σ b (b i)) = ⊤ := by
  have e : (fun i => coordMap σ b (b i)) = ⇑(Pi.basisFun F ι) :=
    funext fun i => (coordMap_basis σ b i).trans (Pi.basisFun_apply _ _ i).symm
  rw [e]
  exact ⟨(Pi.basisFun F ι).linearIndependent, (Pi.basisFun F ι).span_eq⟩

theorem coordMap_image_range : coordMap σ b '' Set.range b = Set.range fun a : ι => (Pi.single a 1 : ι → F) := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext fun i => coordMap_basis σ b i)

end Coord

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (I : NzIn C)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((I.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)

def gapN : TwGap D where
  ntw := C.toTwN I
  nexp := C.toExpN I
  nth := C.toThN I
  ntwbr := C.br
  ntwbr_ind := C.br_ind
  nStage_trivialCharacter_coeff_eq := he
  cover := C.cover

abbrev recN : D7 := withTw D (gapN D C I he)

set_option synthInstance.maxHeartbeats 400000 in

structure EmbC where
  twI : D.what₂.places.Pl → C.Tw
  twI_l : ∀ w, C.l (twI w) = D.what₂.places.resChar w
  embW : ∀ w, D.what₂.LL →+* FractionRing (C.Ok (twI w) 1)
  embW_w : ∀ w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
    embW w x ∈ (algebraMap (C.Ok (twI w) 1) (FractionRing (C.Ok (twI w) 1))).range
  embedding_baseField_condition : ∀ w (x : D.LL0) (y z : C.O0 (twI w)), z ≠ 0 →
    C.emb0 (twI w) x * algebraMap (C.O0 (twI w)) (FractionRing (C.O0 (twI w))) z =
      algebraMap (C.O0 (twI w)) (FractionRing (C.O0 (twI w))) y →
    embW w (x : D.what₂.LL) * algebraMap (C.Ok (twI w) 1) (FractionRing (C.Ok (twI w) 1))
        (algebraMap (C.O (twI w)) (C.Ok (twI w) 1) (algebraMap (C.O0 (twI w)) (C.O (twI w)) z)) =
      algebraMap (C.Ok (twI w) 1) (FractionRing (C.Ok (twI w) 1))
        (algebraMap (C.O (twI w)) (C.Ok (twI w) 1) (algebraMap (C.O0 (twI w)) (C.O (twI w)) y))

variable (E : EmbC D C)

structure StdMt where
  bT : ∀ w j, Module.Basis (I.ixM j) D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  bT_gen : ∀ w j, {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen} = Set.range (bT w j)

variable (S : StdMt D C I)

def eMtN (w : D.what₂.places.Pl) (j : ℕ) :
    D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[E.embW w] (I.ixM j → FractionRing (C.Ok (E.twI w) 1)) :=
  coordMap (E.embW w) (S.bT w j)

theorem eMtN_basis (w : D.what₂.places.Pl) (j : ℕ)
    (b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) :
    LinearIndependent (FractionRing (C.Ok (E.twI w) 1)) (fun i => eMtN D C I E S w j (b i)) ∧
      Submodule.span (FractionRing (C.Ok (E.twI w) 1)) (Set.range fun i => eMtN D C I E S w j (b i)) = ⊤ :=
  haveI : Module.Finite D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := Module.Finite.of_basis (S.bT w j)
  haveI : Finite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) :=
    Module.Finite.finite_basis b
  letI : Fintype (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) := Fintype.ofFinite _
  basis_of_basisF (E.embW w) (coordMap (E.embW w) (S.bT w j)) (S.bT w j)
    (coordMap_good (E.embW w) (S.bT w j)) b

theorem eMtN_lat (w : D.what₂.places.Pl) (j : ℕ) :
    Submodule.span (C.Ok (E.twI w) 1)
      (eMtN D C I E S w j '' {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen}) =
    LinearMap.range (TwCore.incl (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)) (I.ixM j)) := by
  rw [S.bT_gen w j, TwCore.range_incl_eq_span]
  exact congrArg _ (coordMap_image_range (E.embW w) (S.bT w j))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def nchN : NChoice (recN D C I he) :=
  NChoice.ofOk (recN D C I he) E.twI E.twI_l (fun _ => true) (fun _ => ∅) (fun _ => 1) (fun _ => 1) E.embW E.embW_w
    (eMtN D C I E S) (fun w j _ _ _ => eMtN_basis D C I E S w j) (fun w j _ _ _ => eMtN_lat D C I E S w j)

set_option synthInstance.maxHeartbeats 400000 in

theorem nchN_tie : NChTie (recN D C I he) (nchN D C I he E S) where
  twOf_eq := fun a => hL.elim a
  twSide_eq := fun a => hL.elim a
  Q_eq := fun a => hL.elim a
  psi_eq := ⟨fun _ => 1, fun _ => rfl, fun w _ => (map_one (E.embW w)).trans
    (map_one (algebraMap (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)))).symm, fun a => hL.elim a⟩
  embedding_baseField_condition := E.embedding_baseField_condition

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (I : NzIn C)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((I.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (E : EmbC D C)

section One

variable (M : HLat D.what₂.LL) (w : D.what₂.places.Pl) (j : ℕ) (eI : I.ix j → M.ι)

abbrev vE : (I.ix j → FractionRing (C.Ok (E.twI w) 1)) ≃ₗ[C.Ok (E.twI w) 1]
    (C.Ok (E.twI w) 1) ⊗[C.O (E.twI w)] (I.ix j → FractionRing (C.O (E.twI w))) :=
  vecE (C.O (E.twI w)) (C.Ok (E.twI w) 1) (I.ix j) (C.Ok_inj (E.twI w) 1)

def crd (x : M.V) : I.ix j → FractionRing (C.Ok (E.twI w) 1) := fun a => E.embW w (M.b.repr x (eI a))

def eMjN : M.V →+ (C.Ok (E.twI w) 1) ⊗[C.O (E.twI w)] (I.ix j → FractionRing (C.O (E.twI w))) where
  toFun x := vE D C I E w j (crd D C I E M w j eI x)
  map_zero' := by
    have : crd D C I E M w j eI 0 = 0 := funext fun a => by simp [crd]
    rw [this, map_zero]
  map_add' x y := by
    have : crd D C I E M w j eI (x + y) = crd D C I E M w j eI x + crd D C I E M w j eI y :=
      funext fun a => by simp [crd]
    rw [this, map_add]

theorem eMjN_apply (x : M.V) : eMjN D C I E M w j eI x = vE D C I E w j (crd D C I E M w j eI x) := rfl

theorem eMjN_smul (a : D.what₂.LL) (r : C.Ok (E.twI w) 1) (x : M.V)
    (h : E.embW w a = algebraMap (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)) r) :
    eMjN D C I E M w j eI (a • x) = r • eMjN D C I E M w j eI x := by
  have : crd D C I E M w j eI (a • x) = r • crd D C I E M w j eI x := funext fun c => by
    show E.embW w (M.b.repr (a • x) (eI c)) = r • E.embW w (M.b.repr x (eI c))
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, h, Algebra.smul_def]
  rw [eMjN_apply, this, map_smul, eMjN_apply]

theorem exists_int (c : 𝓞 D.what₂.LL) : ∃ r : C.Ok (E.twI w) 1,
    E.embW w (c : D.what₂.LL) = algebraMap (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)) r := by
  obtain ⟨r, hr⟩ := (E.embW_w w (c : D.what₂.LL)).mp
    ((val_nonneg_iff D w _).mpr ((D.plEq w).valuation_le_one c))
  exact ⟨r, hr.symm⟩

variable (hb : Function.Bijective eI)

include hb in
theorem crd_b (a : I.ix j) : crd D C I E M w j eI (M.b (eI a)) = Pi.single a 1 := by
  funext c
  show E.embW w (M.b.repr (M.b (eI a)) (eI c)) = _
  rw [M.b.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : c = a
  · subst h; rw [if_pos rfl, if_pos rfl, map_one]
  · rw [if_neg (fun h' => h (hb.1 h').symm), if_neg h, map_zero]

def sv (a : I.ix j) : (C.Ok (E.twI w) 1) ⊗[C.O (E.twI w)] (I.ix j → FractionRing (C.O (E.twI w))) :=
  vE D C I E w j (Pi.single a 1)

include hb in
theorem eMjN_b (a : I.ix j) : eMjN D C I E M w j eI (M.b (eI a)) = sv D C I E w j a := by
  rw [eMjN_apply, crd_b D C I E M w j eI hb]; rfl

theorem sv_li : LinearIndependent (C.Ok (E.twI w) 1) (sv D C I E w j) :=
  (single_li (C.Ok (E.twI w) 1) (I.ix j) (IsFractionRing.injective _ _)).map' _ (vE D C I E w j).ker

include hb in
theorem eMjN_li : LinearIndependent (C.Ok (E.twI w) 1) (fun a => eMjN D C I E M w j eI (M.b a)) := by
  let e := Equiv.ofBijective eI hb
  have h : (fun a => eMjN D C I E M w j eI (M.b a)) = sv D C I E w j ∘ e.symm := funext fun a => by
    have : a = eI (e.symm a) := (e.apply_symm_apply a).symm
    conv_lhs => rw [this]
    exact eMjN_b D C I E M w j eI hb _
  rw [h]
  exact (sv_li D C I E w j).comp _ e.symm.injective

include hb in
theorem eMjN_span (hM : M.L = Submodule.span (𝓞 D.what₂.LL) (Set.range M.b)) :
    Submodule.span (C.Ok (E.twI w) 1) (eMjN D C I E M w j eI '' (M.L : Set M.V)) =
      Submodule.span (C.Ok (E.twI w) 1) (Set.range (sv D C I E w j)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, hM] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨a', rfl⟩ := hb.2 a
      rw [eMjN_b D C I E M w j eI hb]
      exact Submodule.subset_span ⟨a', rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      obtain ⟨r, hr⟩ := exists_int D C E w c
      rw [← algebraMap_smul D.what₂.LL c x]
      rw [eMjN_smul D C I E M w j eI _ r x hr]
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [← eMjN_b D C I E M w j eI hb]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    rw [SetLike.mem_coe, hM]
    exact Submodule.subset_span ⟨_, rfl⟩

theorem sv_lat : NForms.IsLatIn (Submodule.span (C.Ok (E.twI w) 1) (Set.range (sv D C I E w j))) ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), le_top, fun x _ => ?_⟩
  obtain ⟨z, rfl⟩ := (vE D C I E w j).surjective x
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (C.Ok (E.twI w) 1)) Finset.univ z
  refine ⟨c, nonZeroDivisors.ne_zero c.2, ?_⟩
  have h1 : (c : C.Ok (E.twI w) 1) • z ∈
      LinearMap.range (TwCore.incl (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)) (I.ix j)) :=
    (TwCore.mem_range_incl _).mpr fun y => hc y (Finset.mem_univ y)
  rw [TwCore.range_incl_eq_span] at h1
  rw [← map_smul]
  have h2 := Submodule.mem_map_of_mem (f := (vE D C I E w j).toLinearMap) h1
  rw [Submodule.map_span, ← Set.range_comp] at h2
  exact h2

end One

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (I : NzIn C)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((I.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (E : EmbC D C) (S : StdMt D C I)

theorem trivialSubgroup_eigenspace_top {Γ K V : Type} [Group Γ] [Field K] [AddCommGroup V] [Module K V] (ψ : Γ →* Kˣ) :
    (⨅ u : (⊥ : Subgroup Γ), LinearMap.ker ((scalAct K V ψ u).toLinearMap -
      (((1 : (⊥ : Subgroup Γ) →* Kˣ) u : Kˣ) : K) • LinearMap.id)) = ⊤ := by
  refine iInf_eq_top.mpr fun u => LinearMap.ker_eq_top.mpr ?_
  have hu : u = 1 := Subsingleton.elim _ _
  subst hu
  rw [Subgroup.coe_one, map_one, map_one, Units.val_one, one_smul]
  exact sub_self _

set_option synthInstance.maxHeartbeats 400000 in
theorem nEG_one (i : C.Tw) (j : ℕ) (b : Bool) : NForms.eG (recN D C I he) i j b = 1 :=
  I.hPsi i b (I.ix j → FractionRing (C.O i))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem nFm0_top (i : C.Tw) (j : ℕ) (b : Bool) : NForms.Fm0 (recN D C I he) i j b = ⊤ :=
  trivialSubgroup_eigenspace_top (Γ := G0g D.nd) (K := FractionRing (C.O i)) (V := I.ix j → FractionRing (C.O i)) (I.Psi i)

set_option synthInstance.maxHeartbeats 400000 in
theorem newformsBase_top (i : (recN D C I he).ntw.Tw) (j : ℕ) (b : Bool) : NForms.V0 (recN D C I he) i j b = ⊤ := by
  unfold NForms.V0
  rw [nEG_one D C I he i j b, nFm0_top D C I he i j b]
  exact Submodule.map_id _

set_option synthInstance.maxHeartbeats 400000 in
theorem nV0bc_top (i : (recN D C I he).ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) :
    ((NForms.V0 (recN D C I he) i j b).restrictScalars ((recN D C I he).ntw.O i)).baseChange
      ((recN D C I he).ntw.Ok i k) = ⊤ := by
  rw [newformsBase_top D C I he i j b, Submodule.restrictScalars_top, Submodule.baseChange_top]

variable (X : DivX (recN D C I he))

def mjH (j : ℕ) : HLat D.what₂.LL := X.MjH j

def jMD (j : ℕ) (y : (mjH D C I he X j).V) : D.what₂.Mj j := X.jM j y

structure StdMj where
  eI : ∀ j, I.ix j → (mjH D C I he X j).ι
  eI_bij : ∀ j, 1 ≤ j → j ≤ D.R.m → Function.Bijective (eI j)
  L_std : ∀ j, 1 ≤ j → j ≤ D.R.m →
    (mjH D C I he X j).L = Submodule.span (𝓞 D.what₂.LL) (Set.range (mjH D C I he X j).b)
  th_std : ∀ w j, 1 ≤ j → j ≤ D.R.m → ∀ (x : D.what₂.MtL (D.what₂.muTw w) j) (y : (mjH D C I he X j).V),
    jMD D C I he X j y = D.what₂.thetaP (D.what₂.muTw w) j (D.what₂.jMt (D.what₂.muTw w) j x) →
    ∀ a, (mjH D C I he X j).b.repr y (eI j a) = (S.bT w j).repr x (I.rM j a)

variable (T : StdMj D C I he S X)

theorem eMjN_th (w : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (x : D.what₂.MtL (D.what₂.muTw w) j) (y : (mjH D C I he X j).V)
    (hy : jMD D C I he X j y = D.what₂.thetaP (D.what₂.muTw w) j (D.what₂.jMt (D.what₂.muTw w) j x)) :
    eMjN D C I E (mjH D C I he X j) w j (T.eI j) y =
      vE D C I E w j (LinearMap.funLeft (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)) (I.rM j)
        (eMtN D C I E S w j x)) := by
  rw [eMjN_apply]
  congr 1
  funext a
  exact congrArg (E.embW w) (T.th_std w j h1 h2 x y hy a)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def nmjN : NMj (recN D C I he) X (nchN D C I he E S) where
  eMj := fun w j => eMjN D C I E (mjH D C I he X j) w j (T.eI j)
  eMj_smul := fun w j a r x h => eMjN_smul D C I E (mjH D C I he X j) w j (T.eI j) a r x h
  eMj_li := fun w j _ h1 h2 => eMjN_li D C I E (mjH D C I he X j) w j (T.eI j) (T.eI_bij j h1 h2)
  eMj_lat := fun w j _ h1 h2 => by
    have h := sv_lat D C I E w j
    rw [← eMjN_span D C I E (mjH D C I he X j) w j (T.eI j) (T.eI_bij j h1 h2) (T.L_std j h1 h2)] at h
    have e2 := nV0bc_top D C I he (E.twI w) j true 1
    exact e2.symm ▸ h
  eMj_th := fun w j _ h1 h2 x _ y hy => by
    have h := eMjN_th D C I he E S X T w j h1 h2 x y hy
    have h4 := NChoice.thPe_one (recN D C I he) (nchN D C I he E S) w j (eMtN D C I E S w j x)
    have h6 := NChoice.fracEquiv_symm (K := C.Ok (E.twI w) 1) (eMtN D C I E S w j x)
    exact (congrArg (NChoice.toFracE _ _ w j) h).trans
      (h4.symm.trans (congrArg (NChoice.thPe (recN D C I he) (nchN D C I he E S) w j) h6.symm))

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

theorem TwCore.charZeroK {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} (C : TwCore R H what₂ LL0 N) (i : C.Tw) :
    CharZero (FractionRing (C.O i)) := by
  have h1 : CharZero (FractionRing (C.O0 i)) := charZero_of_injective_ringHom (C.emb0 i).injective
  exact charZero_of_injective_ringHom
    (IsFractionRing.map (A := C.O0 i) (B := C.O i) (K := FractionRing (C.O0 i))
      (L := FractionRing (C.O i)) (C.O_inj i)).injective

namespace NZ

variable {R : Ranks} (H : Host R) (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)
  [NumberField what₂.LL] [StarRing what₂.LL] {LL0 : IntermediateField ℚ what₂.LL}
  (C : TwCore R H what₂ LL0 (ndG H Lb what₂ h))

instance : IsEmpty (ndG H Lb what₂ h).Loc := ⟨fun i => Empty.elim i⟩

def eAlgL (i : C.Tw) : MonoidAlgebra (FractionRing (C.O i)) (G0g (ndG H Lb what₂ h)) :=
  haveI := C.charZeroK i
  e0L H Lb what₂ h (FractionRing (C.O i))

theorem eAlgL_idem (i : C.Tw) : eAlgL H Lb what₂ h C i * eAlgL H Lb what₂ h C i = eAlgL H Lb what₂ h C i :=
  haveI := C.charZeroK i
  labelIdempotent_idem H Lb what₂ h _

theorem eAlgL_central (i : C.Tw) (x) : eAlgL H Lb what₂ h C i * x = x * eAlgL H Lb what₂ h C i :=
  haveI := C.charZeroK i
  labelIdempotent_central H Lb what₂ h _ x

theorem eAlgL_def (i : C.Tw) (b : Bool) (g) : (eAlgL H Lb what₂ h C i).coeff g =
    IsFractionRing.map (A := C.O0 i) (B := C.O i) (K := FractionRing (C.O0 i))
      (L := FractionRing (C.O i)) (C.O_inj i)
      ((if b then C.emb0 i else C.emb0b i) ((qcL H Lb what₂ h g : ℚ) : ↥LL0)) := by
  haveI := C.charZeroK i
  unfold eAlgL
  rw [labelIdempotent_coeff]
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true, map_ratCast]

set_option synthInstance.maxHeartbeats 400000 in

def toExpL : NExp R H what₂ LL0 (ndG H Lb what₂ h) C.toTw where
  Fm _ _ _ := PUnit
  actG _ _ _ := 1
  U := ⊥
  psiU _ _ := 1
  eAlg i _ := eAlgL H Lb what₂ h C i
  eLL0 g := ((qcL H Lb what₂ h g : ℚ) : ↥LL0)
  eAlg_def i b g := eAlgL_def H Lb what₂ h C i b g
  eAlg_idem i _ := eAlgL_idem H Lb what₂ h C i
  eAlg_central i _ x := eAlgL_central H Lb what₂ h C i x
  Bsup _ _ _ := ⊥
  Dat _ _ _ := Empty
  th _ _ _ d := d.elim
  lev _ _ _ d := d.elim
  thPsi _ _ _ _ _ _ d := d.elim
  thPsi_one _ _ _ _ d := d.elim
  thU _ _ _ _ _ d := d.elim
  twPsi _ _ _ _ _ := 0
  twPsi_one _ _ _ _ _ := Subsingleton.elim _ _
  twDel _ _ _ _ _ := 0
  delU _ _ _ := 1
  delU_unr := by intros; rfl
  delU_l := by intros; rfl
  delU_anti _ _ _ _ _ _ := by simp
  delU_open _ _ _ := by simp [MonoidHom.ker_one]
  delU_res := by intros; rfl
  delU_conj _ _ _ _ _ _ _ _ := ⟨1, fun _ => by simp⟩
  MtV _ _ _ _ _ _ := PUnit
  MtLat _ _ _ _ _ _ := ⊥
  MtLat_fg _ _ _ _ _ _ := Submodule.fg_bot
  MtLat_span _ _ _ _ _ _ := Subsingleton.elim _ _
  thP _ _ _ _ _ _ := 0
  hkF _ _ _ _ _ := 1
  embB _ _ _ := 0
  embB_inj _ _ _ _ _ _ := rfl
  eH _ _ _ := 1
  eH_idem _ _ _ := mul_one _

open Classical in
set_option synthInstance.maxHeartbeats 400000 in

def toThL : NTh R H what₂ LL0 (ndG H Lb what₂ h) C.toTw (toExpL H Lb what₂ h C) where
  iC := C.iC
  iC_int := C.iC_int
  aL i := if ∃ k, C.l i = H.g k then 1 else 0
  aL_g i k h := if_pos ⟨k, h⟩
  aL_off i h := if_neg fun ⟨k, hk⟩ => h k hk
  Pt _ _ := Empty
  ev _ _ _ := 0
  ev_smul _ _ _ _ _ y := y.elim
  ev_inj _ _ _ _ _ _ := rfl
  Lt _ _ := PUnit
  Let _ _ := Empty
  Harm _ _ := Set.univ
  Ctr _ _ := Empty
  ctrC _ _ κ := κ.elim
  Harm_def _ _ _ := ⟨fun _ κ => κ.elim, fun _ => trivial⟩
  thV _ _ _ _ y := y.elim
  thV_add _ _ _ _ _ y := y.elim
  thV_smul _ _ _ _ _ y := y.elim
  thV_addP _ _ _ _ _ y := y.elim
  thV_smulP _ _ _ _ _ y := y.elim
  datPhi _ _ _ d := d.elim
  datP _ _ _ d := d.elim
  recDet _ _ y := y.elim
  Kq _ _ _ := PUnit
  actK _ _ _ _ y := y
  actK_one _ _ _ _ := rfl
  actK_mul _ _ _ _ _ _ := rfl
  recDetq _ _ _ y := y.elim
  recDetq_mem _ _ _ y := y.elim
  recDet_act _ _ _ _ y := y.elim
  recDetq_act _ _ _ _ _ y := y.elim
  hkIdx _ _ _ _ := Empty
  hkMove _ _ _ _ c := c.elim
  hkU _ _ _ _ _ c := c.elim
  hk_ev _ _ _ _ _ _ _ _ _ _ y := y.elim
  MaximalUnramifiedExtension _ := ⊤
  FmUr _ _ _ := ⊤
  FmUr_smul := by intros; trivial
  FmUr_span _ _ _ := eq_top_iff.mpr fun x _ => (show x = 0 from rfl) ▸ Submodule.zero_mem _
  Bsup_def _ _ _ := le_antisymm bot_le fun x _ => (show x = 0 from rfl) ▸ Submodule.zero_mem _

end NZ

end Formalism.BasicNotions.Examples₂
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R)

def etaZ (k : Fin 2) : GL (Fin R.r) (ZMod (H.g k)) →* ℤˣ :=
  (quadraticChar (ZMod (H.g k))).toUnitHom.comp Matrix.GeneralLinearGroup.det

theorem exists_etaZ (ht : THyp H) (k : Fin 2) : ∃ x, etaZ H k x = -1 := by
  have hc : ringChar (ZMod (H.g k)) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact (ht.jac k).1
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  have hr : 0 < R.r := Nat.pos_of_ne_zero (r_ne_zero R)
  let M : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g k)) :=
    Matrix.diagonal (Function.update (fun _ => 1) (⟨0, hr⟩ : Fin R.r) (a : ZMod (H.g k)))
  have hdet : M.det = a := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact a.ne_zero), Units.ext ?_⟩
  show quadraticChar (ZMod (H.g k)) (Matrix.det M) = -1
  rw [hdet, ha]

variable (K : Type) [Field K] [CharZero K]

def psiU (k : Fin 2) (v : Fin R.f) : GL (Fin R.r) (ZMod (H.g k)) →* Kˣ :=
  if v.1 ≠ 0 then (Units.map (Int.castRingHom K).toMonoidHom).comp (etaZ H k) else 1

variable (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)

def PsiU : G0g (ndG H Lb what₂ h) →* Kˣ :=
  ∏ kv : Ix (ndG H Lb what₂ h), (psiU H K kv.1 kv.2).comp (Pi.evalMonoidHom _ kv)

theorem PsiU_apply (g : G0g (ndG H Lb what₂ h)) :
    ((PsiU H K Lb what₂ h g : Kˣ) : K) = ∏ kv : Ix (ndG H Lb what₂ h), ((psiU H K kv.1 kv.2 (g kv) : Kˣ) : K) := by
  unfold PsiU
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  rfl

theorem monicOf_eq_iff {k : Fin 2} (f : (ZMod (H.g k))[X]) (hm : f.Monic) (hd : f.natDegree = R.r)
    (a : Fin R.r → ZMod (H.g k)) : Formalism.CyclotomicNorms.monicOf a = f ↔ a = fun i : Fin R.r => f.coeff i := by
  constructor
  · intro e
    funext i
    rw [← e, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]
  · intro e
    rw [e]
    exact Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f hm hd

theorem evS_eSum' {K : Type} [Field K] {I : Type} [Fintype I] [dI : DecidableEq I] {G : I → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {L : I → Type} [∀ i, Fintype (L i)] (E : ∀ i, L i → MonoidAlgebra K (G i))
    (S : (∀ i, L i) → Prop) (ψ : ∀ i, G i → K) (b : ∀ i, L i) (hb : S b)
    (h1 : ∀ i, evS (ψ i) (E i (b i)) = 1) (h0 : ∀ i l, l ≠ b i → evS (ψ i) (E i l) = 0) :
    evS (fun g : ∀ i, G i => ∏ i, ψ i (g i)) (@eSum K _ I _ G _ _ L _ dI E S) = 1 := by
  unfold eSum
  rw [evS_sum, Finset.sum_eq_single b]
  · rw [if_pos hb, evS_tens]
    exact Finset.prod_eq_one fun i _ => h1 i
  · intro a _ hab
    split_ifs
    · rw [evS_tens]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
      exact Finset.prod_eq_zero (Finset.mem_univ i) (h0 i _ hi)
    · exact evS_zero _
  · intro h; exact absurd (Finset.mem_univ _) h

omit [CharZero K] in

theorem evS_e0F {what₂ : Rows.Data R} (N : NData R H what₂)
    (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k))))
    (ψ : ∀ kv : Ix N, GL (Fin R.r) (ZMod (H.g kv.1)) → K) (f : ∀ k, N.PlG k → (ZMod (H.g k))[X]) (hf : GoodT N f)
    (hδ : ∀ (kv : Ix N) (p : (ZMod (H.g kv.1))[X]), evS (ψ kv) (es kv.1 p) = if p = f kv.1 kv.2 then 1 else 0) :
    evS (fun g : G0g N => ∏ kv, ψ kv (g kv)) (e0F N es) = 1 := by
  have hm : ∀ k v, Formalism.CyclotomicNorms.monicOf (fun i : Fin R.r => (f k v).coeff i) = f k v := fun k v =>
    Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ ((hf k).1.1 v).1 ((hf k).1.1 v).2.1
  have hb : GoodT N (fun k v => Formalism.CyclotomicNorms.monicOf (fun i : Fin R.r => (f k v).coeff i)) := by
    have : (fun k v => Formalism.CyclotomicNorms.monicOf (fun i : Fin R.r => (f k v).coeff i)) = f :=
      funext fun k => funext fun v => hm k v
    rw [this]; exact hf
  have hd1 : ∀ kv : Ix N, evS (ψ kv) (es kv.1 (Formalism.CyclotomicNorms.monicOf fun i : Fin R.r => (f kv.1 kv.2).coeff i)) = 1 :=
    fun kv => by rw [hδ, if_pos (hm _ _)]
  have hd0 : ∀ (kv : Ix N) (a : Fin R.r → ZMod (H.g kv.1)), a ≠ (fun i : Fin R.r => (f kv.1 kv.2).coeff i) →
      evS (ψ kv) (es kv.1 (Formalism.CyclotomicNorms.monicOf a)) = 0 := fun kv a e => by
    rw [hδ, if_neg (fun e' => e ((monicOf_eq_iff H _ ((hf kv.1).1.1 kv.2).1 ((hf kv.1).1.1 kv.2).2.1 a).mp e'))]
  exact evS_eSum' (I := Ix N) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
    (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => es kv.1 (Formalism.CyclotomicNorms.monicOf a))
    (fun a => GoodT N fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ψ
    (fun kv => fun i : Fin R.r => (f kv.1 kv.2).coeff i) hb hd1 hd0

theorem evS_e0L (ht : THyp H) :
    evS (fun g => ((PsiU H K Lb what₂ h g : Kˣ) : K)) (e0L H Lb what₂ h K) = 1 := by
  have e : (fun g => ((PsiU H K Lb what₂ h g : Kˣ) : K)) =
      fun g : G0g (ndG H Lb what₂ h) => ∏ kv : Ix (ndG H Lb what₂ h), ((psiU H K kv.1 kv.2 (g kv) : Kˣ) : K) :=
    funext fun g => PsiU_apply H K Lb what₂ h g
  rw [e]
  refine evS_e0F H K (ndG H Lb what₂ h) (esL Lb K) (fun kv x => ((psiU H K kv.1 kv.2 x : Kˣ) : K)) (tupL Lb)
    (goodT_tupL H Lb what₂ h) ?_
  rintro ⟨k, v⟩ p
  have hv' : (v : Fin R.f).1 ≠ 0 ∨ (v : Fin R.f).1 = 0 := (em _).symm
  show evS (fun x => ((psiU H K k v x : Kˣ) : K)) (esZ K _ (Lb.fA k) (Lb.fB k) p) = if p = tupL Lb k v then 1 else 0
  rcases hv' with hv | hv
  · obtain ⟨x, hx⟩ := exists_etaZ H ht k
    have hψ : (fun y => ((psiU H K k v y : Kˣ) : K)) =
        ⇑((Units.coeHom K).comp ((Units.map (Int.castRingHom K).toMonoidHom).comp (etaZ H k))) := by
      funext y; unfold psiU; rw [if_pos hv]; rfl
    rw [hψ, evS_esZ_ne (Lb.ne k) _ x (by
      show (((etaZ H k x : ℤˣ) : ℤ) : K) ≠ 1
      rw [hx]; norm_num)]
    have ht' : tupL Lb k v = Lb.fA k := by unfold tupL; rw [if_pos (by simpa using hv)]
    rw [ht']
    split_ifs <;> rfl
  · have hψ : (fun y => ((psiU H K k v y : Kˣ) : K)) = fun _ => 1 := by
      funext y; unfold psiU; rw [if_neg (not_not.mpr hv)]; rfl
    rw [hψ, evS_esZ_one (Lb.ne k)]
    have ht' : tupL Lb k v = Lb.fB k := by unfold tupL; rw [if_neg (by simpa using hv)]
    rw [ht']
    split_ifs <;> rfl

variable (V : Type) [AddCommGroup V] [Module K V]

def actGL : G0g (ndG H Lb what₂ h) →* (V ≃ₗ[K] V) where
  toFun g := LinearEquiv.smulOfUnit (PsiU H K Lb what₂ h g)
  map_one' := by
    ext x
    show PsiU H K Lb what₂ h 1 • x = x
    rw [map_one, one_smul]
  map_mul' a b := by
    ext x
    show PsiU H K Lb what₂ h (a * b) • x = PsiU H K Lb what₂ h a • PsiU H K Lb what₂ h b • x
    rw [map_mul, mul_smul]

theorem lift_actGL (ht : THyp H) :
    MonoidAlgebra.lift K (Module.End K V) (G0g (ndG H Lb what₂ h))
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (actGL H K Lb what₂ h V)) (e0L H Lb what₂ h K) = 1 := by
  rw [lift_scalar ((Units.coeHom K).comp (PsiU H K Lb what₂ h)) _ (fun g => by ext x; rfl)]
  show evS (fun g => ((PsiU H K Lb what₂ h g : Kˣ) : K)) _ • (1 : Module.End K V) = 1
  rw [evS_e0L H K Lb what₂ h ht, one_smul]

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

section Emb

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (I : NzIn C)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((I.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (hLL0 : ∀ x : D.what₂.LL, x ∈ D.LL0)

set_option synthInstance.maxHeartbeats 400000 in
theorem embedding_baseField_mul (R : D7) (hR : ∀ x : R.what₂.LL, x ∈ R.LL0) (i : R.ntw.Tw) (x : R.LL0) (y z : R.ntw.O0 i)
    (h : R.ntw.emb0 i x * algebraMap (R.ntw.O0 i) (FractionRing (R.ntw.O0 i)) z =
      algebraMap (R.ntw.O0 i) (FractionRing (R.ntw.O0 i)) y) :
    embAt R hR i (x : R.what₂.LL) * algebraMap (R.ntw.Ok i 1) (FractionRing (R.ntw.Ok i 1))
        (algebraMap (R.ntw.O i) (R.ntw.Ok i 1) (algebraMap (R.ntw.O0 i) (R.ntw.O i) z)) =
      algebraMap (R.ntw.Ok i 1) (FractionRing (R.ntw.Ok i 1))
        (algebraMap (R.ntw.O i) (R.ntw.Ok i 1) (algebraMap (R.ntw.O0 i) (R.ntw.O i) y)) := by
  have h1 := congrArg (iotaOk R i 1) h
  rw [map_mul, iotaOk_alg, iotaOk_alg] at h1
  have h2 : toLL0 R hR (x : R.what₂.LL) = x := Subtype.ext rfl
  show iotaOk R i 1 (R.ntw.emb0 i (toLL0 R hR (x : R.what₂.LL))) * _ = _
  rw [h2]
  exact h1

set_option synthInstance.maxHeartbeats 400000 in

def embCOf : EmbC D C where
  twI := fun w => (cover_at (recN D C I he) hLL0 C.cover w).choose
  twI_l := fun w => (cover_at (recN D C I he) hLL0 C.cover w).choose_spec.1
  embW := fun w => embAt (recN D C I he) hLL0 (cover_at (recN D C I he) hLL0 C.cover w).choose
  embW_w := fun w x => embAt_w (recN D C I he) hLL0 w _ (cover_at (recN D C I he) hLL0 C.cover w).choose_spec.2 x
  embedding_baseField_condition := fun w x y z _ h => embedding_baseField_mul (recN D C I he) hLL0 _ x y z h

end Emb

section Good

variable {R : Ranks} (H : Host R) (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)
  [NumberField what₂.LL] [StarRing what₂.LL] {LL0 : IntermediateField ℚ what₂.LL}
  (C : TwCore R H what₂ LL0 (ndG H Lb what₂ h)) (ht : THyp H) (n : ℕ)

set_option synthInstance.maxHeartbeats 400000 in

def nzInL : NzIn C where
  eA i _ := eAlgL H Lb what₂ h C i
  eL g := ((qcL H Lb what₂ h g : ℚ) : ↥LL0)
  eA_def i b g := eAlgL_def H Lb what₂ h C i b g
  eA_idem i _ := eAlgL_idem H Lb what₂ h C i
  eA_central i _ x := eAlgL_central H Lb what₂ h C i x
  Psi i := haveI := C.charZeroK i; PsiU H (FractionRing (C.O i)) Lb what₂ h
  hPsi i _ V _ _ := by
    have := C.charZeroK i
    have e : scalAct (FractionRing (C.O i)) V (PsiU H (FractionRing (C.O i)) Lb what₂ h) =
        actGL H (FractionRing (C.O i)) Lb what₂ h V := by
      ext g x; rfl
    unfold eAlgL
    rw [e]
    exact lift_actGL H (FractionRing (C.O i)) Lb what₂ h V ht
  ix j := {_a : Fin n // 1 ≤ j ∧ j ≤ R.m}
  ix_out _ := fun ⟨a⟩ => a.2
  ixM _ := Fin n
  rM _ := Subtype.val

end Good

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

section E

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂}

set_option synthInstance.maxHeartbeats 400000 in

structure NzE (C : TwCore R H what₂ LL0 N) : Type 1 where
  eA : ∀ i, Bool → MonoidAlgebra (FractionRing (C.O i)) (G0g N)
  eL : G0g N → LL0
  eA_def : ∀ i b (g : G0g N), (eA i b).coeff g =
    IsFractionRing.map (A := C.O0 i) (B := C.O i) (K := FractionRing (C.O0 i))
      (L := FractionRing (C.O i)) (C.O_inj i) ((if b then C.emb0 i else C.emb0b i) (eL g))
  eA_idem : ∀ i b, eA i b * eA i b = eA i b
  eA_central : ∀ i b x, eA i b * x = x * eA i b
  Psi : ∀ i, G0g N →* (FractionRing (C.O i))ˣ
  hPsi : ∀ i b (V : Type) [AddCommGroup V] [Module (FractionRing (C.O i)) V],
    MonoidAlgebra.lift (FractionRing (C.O i)) (Module.End (FractionRing (C.O i)) V) (G0g N)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (scalAct _ V (Psi i))) (eA i b) = 1

abbrev NzE.toIn {C : TwCore R H what₂ LL0 N} (Ed : NzE C) (n : ℕ → ℕ) : NzIn C where
  eA := Ed.eA
  eL := Ed.eL
  eA_def := Ed.eA_def
  eA_idem := Ed.eA_idem
  eA_central := Ed.eA_central
  Psi := Ed.Psi
  hPsi := Ed.hPsi
  ix j := {_a : Fin (n j) // 1 ≤ j ∧ j ≤ R.m}
  ix_out _ := fun ⟨a⟩ => a.2
  ixM j := Fin (n j)
  rM _ := Subtype.val

end E

def nzEL {R : Ranks} (H : Host R) (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)
    [NumberField what₂.LL] [StarRing what₂.LL] {LL0 : IntermediateField ℚ what₂.LL}
    (C : TwCore R H what₂ LL0 (ndG H Lb what₂ h)) (ht : THyp H) : NzE C :=
  let I := nzInL H Lb what₂ h C ht 0
  ⟨I.eA, I.eL, I.eA_def, I.eA_idem, I.eA_central, I.Psi, I.hPsi⟩

theorem jB_gen_set {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V) :
    {x | jB σ b x ∈ genB b} = Set.range (Pi.basisFun K (Fin n)) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (show jB σ b x ∈ Finset.univ.image b from hx)
    exact ⟨i, jB_inj σ b ((jB_single σ b i).trans hi)⟩
  · rintro ⟨i, rfl⟩
    exact (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (jB_single σ b i).symm⟩ :
      jB σ b (Pi.basisFun K (Fin n) i) ∈ Finset.univ.image b)

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (Ed : NzE C) (n : ℕ → ℕ)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((Ed.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)

structure StdRows where
  bt : ∀ w j, OrthonormalBasis (Fin (n j)) ℂ (D.what₂.Mt (D.what₂.muTw w) j)
  phi : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j ≃ₗ[D.what₂.LL] (Fin (n j) → D.what₂.LL)
  hj : ∀ w j x, D.what₂.jMt (D.what₂.muTw w) j x = jB D.what₂.embLL (bt w j) (phi w j x)
  hgen : ∀ w j, (D.what₂.MtLat (D.what₂.muTw w) j).gen = genB (bt w j)
  bM : ∀ j, OrthonormalBasis (Fin (n j)) ℂ (D.what₂.Mj j)
  hgM : ∀ j, (D.what₂.MjLat j).gen = genB (bM j)
  hth : ∀ w j (x : Fin (n j) → D.what₂.LL),
    D.what₂.thetaP (D.what₂.muTw w) j (jB D.what₂.embLL (bt w j) x) = jB D.what₂.embLL (bM j) x

variable (Z : StdRows D n)

def stdMtOf : StdMt D C (Ed.toIn n) where
  bT := fun w j => (Pi.basisFun D.what₂.LL (Fin (n j))).map (Z.phi w j).symm
  bT_gen := fun w j => by
    ext x
    rw [Set.mem_setOf_eq, Z.hj, Z.hgen]
    have h := Set.ext_iff.mp (jB_gen_set D.what₂.embLL (Z.bt w j)) (Z.phi w j x)
    rw [Set.mem_setOf_eq] at h
    rw [h]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [Module.Basis.map_apply, hi, LinearEquiv.symm_apply_apply]⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [← hi, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]⟩

def divXOf : DivX (recN D C (Ed.toIn n) he) :=
  divXStd (recN D C (Ed.toIn n) he) n Z.bM Z.hgM 1 one_pos

def stdMjOf : StdMj D C (Ed.toIn n) he (stdMtOf D C Ed n Z) (divXOf D C Ed n he Z) where
  eI := fun _ a => a.1
  eI_bij := fun _ h1 h2 => ⟨fun _ _ h => Subtype.ext h, fun a => ⟨⟨a, h1, h2⟩, rfl⟩⟩
  L_std := fun _ _ _ => rfl
  th_std := fun w j _ _ x y hy a => by
    have h1 : jB D.what₂.embLL (Z.bM j) y = jB D.what₂.embLL (Z.bM j) (Z.phi w j x) := by
      rw [← Z.hth w j, ← Z.hj]; exact hy
    have h2 : y = Z.phi w j x := jB_inj _ _ h1
    show (Pi.basisFun D.what₂.LL (Fin (n j))).repr y a.1 =
      ((Pi.basisFun D.what₂.LL (Fin (n j))).map (Z.phi w j).symm).repr x a.1
    rw [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm, h2]

variable (hLL0 : ∀ x : D.what₂.LL, x ∈ D.LL0)

def nchStd : NChoice (recN D C (Ed.toIn n) he) :=
  nchN D C (Ed.toIn n) he (embCOf D C (Ed.toIn n) he hLL0) (stdMtOf D C Ed n Z)


end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Rec

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

local notation "DR" => (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)

instance levelRecordLocalSetEmpty : IsEmpty (DR).nd.Loc := ⟨fun i => Empty.elim i⟩

def levelRecordStandardData : StdRows DR fun _ => d0 where
  bt := fun _ _ => eb d0
  phi := fun _ _ => LinearEquiv.refl _ _
  hj := fun _ _ _ => rfl
  hgen := fun _ _ => rfl
  bM := fun _ => eb d0
  hgM := fun _ => rfl
  hth := fun _ _ _ => rfl

abbrev row_E (C : TwCore (DR).R (DR).host (DR).what₂ (DR).LL0 (DR).nd) : NzE C := nzEL H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) C ht

theorem row_he (C : TwCore (DR).R (DR).host (DR).what₂ (DR).LL0 (DR).nd) : ∀ g, (DR).what₂.embLL (((row_E H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat C).eL g : ↥(DR).LL0) : (DR).what₂.LL) = (DR).ntypes.e0.coeff g :=
  fun g => labelIdempotent_baseField H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) ⊤ ht G.tame g

abbrev levelRecordTwistGap (C : TwCore (DR).R (DR).host (DR).what₂ (DR).LL0 (DR).nd) : TwGap DR := gapN DR C ((row_E H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat C).toIn fun _ => d0) (row_he H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat C)

theorem rows_mem_baseField : ∀ x : (DR).what₂.LL, x ∈ (DR).LL0 := fun _ => trivial

def fin_nch (C : TwCore (DR).R (DR).host (DR).what₂ (DR).LL0 (DR).nd) : NChoice (withTw DR (levelRecordTwistGap H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat C)) :=
  nchStd DR C (row_E H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat C) (fun _ => d0) (row_he H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat C) (levelRecordStandardData H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) (rows_mem_baseField H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)


end Rec

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.Inhab

section LevelValuationRings

variable {R : Ranks} (H : Host R) {W : Type} (hcW : W → Tau2 R → HCParam R) (K : W → ClsPkg) (T : W → ℕ)
  (rOf : W → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : W → ℕ → Set ↥(R.Psi))

def localDataAtServedPlace' : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w) := fun u w h =>
  gatNZ (served_of h) (bs u ((@placesOf H.E _ _ H.cmStar).resChar w)) (rOf u ((@placesOf H.E _ _ H.cmStar).resChar w))
    (fun ψ => lamOf (hcW u ψ) 0) ((K u).cls 0) (eOf ((@placesOf H.E _ _ H.cmStar).resChar w))

theorem localData_rank_eq_classes : ∀ u w h, (localDataAtServedPlace' H hcW K T rOf eOf bs u w h).d = Fintype.card ((K u).cls 0) := fun _ _ _ => by
  classical
  exact gatNZ_d _ _ _ _ _ _

end LevelValuationRings

section Rec

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
variable (rOf : W → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : W → ℕ → Set ↥(R.Psi))

variable (Wg : TwGap (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL (localDataAtServedPlace' H hcW K T rOf eOf bs) (localData_rank_eq_classes H hcW K T rOf eOf bs)))

local notation "DG" => (withTw (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL (localDataAtServedPlace' H hcW K T rOf eOf bs) (localData_rank_eq_classes H hcW K T rOf eOf bs)) Wg)

def fin_gatTies : GatTies DG where
  gat_k := fun _ _ _ => k_pos R
  gat_n := fun _ _ h _ P hP hL σ hσ => @orderOf_frobenius_image_eq _ H _ (served_of h) P hP hL σ hσ
  gat_pos := fun u w h => (posPsi (served_of h) (bs u ((@placesOf H.E _ _ H.cmStar).resChar w))).trans (Equiv.refl _).symm
  gat_step := fun u w h v s P hP hL σ hσ =>
    @position_succ_eq_mul_frobenius _ H _ (served_of h) (bs u ((@placesOf H.E _ _ H.cmStar).resChar w)) _ (Equiv.refl _) v s P hP hL σ hσ
  gat_lam := fun _ _ _ _ _ _ => rfl

end Rec

end Formalism.BasicNotions.Examples₂.NZ
end
end
