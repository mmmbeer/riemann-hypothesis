import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspLatticeAnyLevel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnipotentLatticeMembership
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients

noncomputable section

namespace GlobalTheory.GoodLatCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership

section Clause

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G']


theorem mjFull_iff (A : FormsL LL Ks WL W G) (J0 : Subgroup G) (lam0 : J0 →* LLˣ) (eC : G → LL) :
    MjFull A J0 lam0 eC ↔ MjLattice A J0 lam0 eC := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨b, hb⟩ := exists_isGoodBasis A J0 lam0 eC
    exact ⟨⟨_, b, hb⟩, fun d b hb => ⟨hb, h2 d b hb⟩⟩
  · rintro ⟨⟨d, b, hb⟩, h2⟩
    refine ⟨?_, fun d b hb => (h2 d b hb).2⟩
    rw [← hb.2]
    exact FiniteDimensional.span_of_finite LL (Set.finite_range b)

omit [NumberField LL] in

theorem isCentralIdem_comp (e : G' ≃* G) {eC : G → LL} (h : IsCentralIdem eC) : IsCentralIdem (fun g => eC (e g)) :=
  ⟨fun g x => by simpa using h.1 (e g) (e x), fun g => by
    refine Eq.trans ?_ (h.2 (e g))
    exact Fintype.sum_equiv e.toEquiv _ _ fun x => by simp⟩

end Clause

section Forms

variable {D : D7} (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
  [Module (𝓞 T.Q.c.F) WL] [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G]

theorem isFormsOf_of_carriesCusp {A : FormsL LL T.Q.c.F WL W G} {ι : Cusp T j w →ₗ[T.Q.c.F] WL}
    (h : CarriesCusp T j w A ι) : IsFormsOf T j (wtA w) w.n A ι := by
  refine ⟨h.1, h.2.1, fun f => ?_⟩
  have hf : ι f ∈ A.WK := h.2.1 ▸ LinearMap.mem_range_self ι f
  exact ⟨fun ⟨h', hh⟩ lp => (h.2.2 lp f h').1 (hh lp), fun hh => ⟨hf, fun lp => (h.2.2 lp f hf).2 (hh lp)⟩⟩

theorem injective_of_baseChange {K L M N : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module L N] [IsScalarTower K L N] {ι : M →ₗ[K] N} (h : IsBaseChange L ι) :
    Function.Injective ι := by
  intro x y hxy
  apply incl_injective (K := K) (L := L) (M := M)
  apply h.equiv.injective
  show h.equiv (1 ⊗ₜ x) = h.equiv (1 ⊗ₜ y)
  rw [h.equiv_tmul, h.equiv_tmul, hxy]

theorem exists_carriesCusp {A : FormsL LL T.Q.c.F WL W G} {ι : Cusp T j w →ₗ[T.Q.c.F] WL}
    (h : IsFormsOf T j (wtA w) w.n A ι) :
    ∃ A' : FormsL LL T.Q.c.F WL W G, CarriesCusp T j w A' ι ∧ A'.MK = A.MK ∧ A'.ρ = A.ρ ∧ A'.chi = A.chi := by
  have hi := injective_of_baseChange h.1
  let u := (LinearEquiv.ofInjective ι hi).symm
  have hu : ∀ f hf, u ⟨ι f, hf⟩ = f := fun f hf => by rw [LinearEquiv.symm_apply_eq]; rfl
  let A' : FormsL LL T.Q.c.F WL W G :=
    { WK := LinearMap.range ι
      Pt := T.PtM j
      nrm := fun lp y x => T.nrmM j lp y (u x : T.R j)
      nrm_nonneg := fun lp y x => (nrmM_laws T j lp y).1 _
      nrm_zero := fun lp y => by rw [map_zero]; exact (nrmM_laws T j lp y).2.1
      nrm_add := fun lp y x x' => by rw [map_add]; exact (nrmM_laws T j lp y).2.2.1 _ _
      nrm_smul := fun lp y a x => by rw [u.map_smul]; exact (nrmM_laws T j lp y).2.2.2 _ _
      towKs := A.towKs, ρ := A.ρ, chi := A.chi, j := A.j }
  have hc : CarriesCusp T j w A' ι := ⟨h.1, rfl, fun lp f hf => forall_congr' fun y => by
    show T.nrmM j lp y (u ⟨ι f, hf⟩ : T.R j) ≤ 1 ↔ _
    rw [hu]⟩
  refine ⟨A', hc, ?_, rfl, rfl⟩
  have h' := isFormsOf_of_carriesCusp T j w hc
  ext x
  constructor
  · intro hx
    obtain ⟨f, rfl⟩ : x ∈ LinearMap.range ι := hx.1
    exact (h.2.2 f).2 ((h'.2.2 f).1 hx)
  · intro hx
    obtain ⟨f, rfl⟩ : x ∈ LinearMap.range ι := h.2.1 ▸ hx.1
    exact (h'.2.2 f).2 ((h.2.2 f).1 hx)

end Forms

section Local

variable {κ κ' : Type} [CommRing κ] [CommRing κ'] {r : ℕ}

def glEquiv (i : κ ≃+* κ') (r : ℕ) : GL (Fin r) κ ≃ GL (Fin r) κ' where
  toFun := Matrix.GeneralLinearGroup.map (i : κ →+* κ')
  invFun := Matrix.GeneralLinearGroup.map (i.symm : κ' →+* κ)
  left_inv g := by ext a b; simp
  right_inv g := by ext a b; simp

theorem edgeSum_map (i : κ ≃+* κ') (g : GL (Fin r) κ) :
    edgeSum supEdge (Matrix.GeneralLinearGroup.map (i : κ →+* κ') g) = i (edgeSum supEdge g) := by
  unfold edgeSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · rfl
  · rw [map_zero]

end Local

structure PlaceIso (D : D7) (Pg : Finset (Pl D.host.E)) where
  pl : TypePl D ≃ ↥Pg
  iso : ∀ v : TypePl D, ZMod (D.host.g v.1) ≃+* kP (pl v).1

namespace PlaceIso

variable {D : D7} {Pg : Finset (Pl D.host.E)} (P : PlaceIso D Pg) {LL : Type} [Field LL]

def grp : G0g D.nd ≃* G0 Pg D.R.r where
  toEquiv := (Equiv.piCongrRight fun v => glEquiv (P.iso v) D.R.r).trans
    (Equiv.piCongrLeft (fun PP : ↥Pg => GL (Fin D.R.r) (kP PP.1)) P.pl)
  map_mul' x y := by
    funext PP
    obtain ⟨v, rfl⟩ := P.pl.surjective PP
    simp [glEquiv]

theorem grp_apply (g : G0g D.nd) (v : TypePl D) :
    P.grp g (P.pl v) = Matrix.GeneralLinearGroup.map (P.iso v : ZMod (D.host.g v.1) →+* kP (P.pl v).1) (g v) := by
  simp [grp, glEquiv]

def pullChi (χ : ∀ PP : ↥Pg, (kP PP.1)ˣ →* LLˣ) (v : TypePl D) : (ZMod (D.host.g v.1))ˣ →* LLˣ :=
  (χ (P.pl v)).comp (Units.map (P.iso v : ZMod (D.host.g v.1) →+* kP (P.pl v).1).toMonoidHom)

def pullPsi (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) LL) (v : TypePl D) : AddChar (ZMod (D.host.g v.1)) LL :=
  (ψ (P.pl v).1).compAddMonoidHom (P.iso v).toAddMonoidHom

theorem lamP0_pull_psi (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) LL) (g : G0g D.nd) (h' : g ∈ unipG D)
    (h : P.grp g ∈ (P0 Pg D.R.r ψ).conj.H) :
    unipotentCharacterOfAddChars D (P.pullPsi ψ) ⟨g, h'⟩ = (P0 Pg D.R.r ψ).conj.chi ⟨P.grp g, h⟩ := by
  unfold unipotentCharacterOfAddChars LevelP.conj P0 LevelP.ofLocal
  simp only [MonoidHom.inv_apply, MonoidHom.finsetProd_apply]
  congr 1
  refine Fintype.prod_equiv P.pl _ _ fun v => Units.ext ?_
  show ψ (P.pl v).1 (P.iso v (edgeSum supEdge (g v))) = ψ (P.pl v).1 (edgeSum supEdge (P.grp g (P.pl v)))
  rw [grp_apply, edgeSum_map]

end PlaceIso

section Places

open scoped Pointwise

variable {D : D7}

theorem map_le_iff_under (Q : HeightOneSpectrum (𝓞 D.host.K)) (PP : Pl D.host.E) :
    Q.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal ↔ PP.under (𝓞 D.host.K) = Q := by
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · intro h
    exact HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (PP.under (𝓞 D.host.K)).isPrime.ne_top h).symm
  · rintro rfl
    exact le_rfl

theorem over_of_under {k : Fin 2} {Q : HeightOneSpectrum (𝓞 D.host.K)}
    (hQ : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ Q.asIdeal) {PP : Pl D.host.E} (h : PP.under (𝓞 D.host.K) = Q) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  subst h
  have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hQ
  rwa [map_natCast] at this

theorem finite_over (k : Fin 2) : (placesOver D.host.E (D.host.g k)).Finite :=
  Set.finite_of_ncard_ne_zero (by rw [D.nd.g_split k]; exact Module.finrank_pos.ne')

theorem ncard_under {k : Fin 2} {Q : HeightOneSpectrum (𝓞 D.host.K)}
    (hQ : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ Q.asIdeal) :
    {PP : Pl D.host.E | PP.under (𝓞 D.host.K) = Q}.ncard = D.R.f := by
  have hE : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    have h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
      rw [D.host.finrank_cmField]
      unfold Ranks.f Ranks.n
      push_cast
      ring
    exact_mod_cast h
  let c : Pl D.host.E → Pl D.host.E := fun w => ⟨D.host.conj • w.asIdeal, haveI := w.isPrime; inferInstance, by
    intro h0
    apply w.ne_bot
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this⟩
  have hci : Function.Injective c := fun a b h => HeightOneSpectrum.ext
    (MulAction.injective D.host.conj (congrArg HeightOneSpectrum.asIdeal h))
  have hm := fun w hw => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k)
    w hw).2.2.2 Q hQ (c w) ((GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj w (c w)).2 rfl)
  set S := {PP : Pl D.host.E | PP.under (𝓞 D.host.K) = Q}
  set X := placesOver D.host.E (D.host.g k)
  have hX : X.Finite := finite_over k
  have hS : S ⊆ X := fun w hw => over_of_under hQ hw
  have h1 : S.ncard ≤ (X \ S).ncard :=
    Set.ncard_le_ncard_of_injOn c (fun w hw => ⟨(hm w (hS hw)).1, (hm w (hS hw)).2.1 hw⟩) hci.injOn hX.diff
  have h2 : (X \ S).ncard ≤ S.ncard :=
    Set.ncard_le_ncard_of_injOn c (fun w hw => not_not.1 fun h => hw.2 ((hm w hw.1).2.2 h)) hci.injOn (hX.subset hS)
  have h3 := Set.ncard_diff_add_ncard_of_subset hS hX
  have h4 : X.ncard = 2 * D.R.f := (D.nd.g_split k).trans hE
  omega

variable {T : Core D} (hb : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal)
include hb

theorem nonempty_placeIso {Pg : Finset (Pl D.host.E)} (h : IsTypeSet T Pg) : Nonempty (PlaceIso D Pg) := by
  have he : ∀ k, Nonempty (D.nd.PlG k ≃ {PP : Pl D.host.E | PP.under (𝓞 D.host.K) = T.pb k}) := by
    intro k
    haveI : Finite {PP : Pl D.host.E | PP.under (𝓞 D.host.K) = T.pb k} :=
      (finite_over k).subset fun w hw => over_of_under (hb k) hw
    rw [← Finite.card_eq, Nat.card_coe_set_eq, ncard_under (hb k), Nat.card_eq_fintype_card, D.nd.card_PlG]
  let e := fun k => (he k).some
  let p : TypePl D → ↥Pg := fun v => ⟨(e v.1 v.2).1, (h _).2 ⟨v.1, (map_le_iff_under _ _).2 (e v.1 v.2).2⟩⟩
  have hov : ∀ v, ((D.host.g v.1 : ℕ) : 𝓞 D.host.E) ∈ (p v).1.asIdeal := fun v => over_of_under (hb v.1) (e v.1 v.2).2
  have hN : ∀ v, Ideal.absNorm (p v).1.asIdeal = D.host.g v.1 := fun v =>
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime v.1) (D.nd.g_split v.1) _ (hov v)).1
  have hp : Function.Bijective p := by
    constructor
    · rintro ⟨k, a⟩ ⟨k', a'⟩ hh
      have hg : D.host.g k = D.host.g k' := (hN ⟨k, a⟩).symm.trans (hh ▸ hN ⟨k', a'⟩)
      obtain rfl : k = k' := by
        have := D.host.g_ne
        fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd hg this | exact absurd hg.symm this
      obtain rfl : a = a' := (e k).injective (Subtype.ext (congrArg (fun x : ↥Pg => x.1) hh))
      rfl
    · rintro ⟨PP, hP⟩
      obtain ⟨k, hk⟩ := (h PP).1 hP
      exact ⟨⟨k, (e k).symm ⟨PP, (map_le_iff_under _ _).1 hk⟩⟩, Subtype.ext (by simp [p])⟩
  refine ⟨⟨Equiv.ofBijective p hp, fun v => ?_⟩⟩
  have hc : Nat.card (kP (p v).1) = D.host.g v.1 := by
    rw [← hN v, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (kP (p v).1) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime v.1).ne_zero)
  haveI := Fintype.ofFinite (kP (p v).1)
  exact ZMod.ringEquivOfPrime (kP (p v).1) (D.host.g_prime v.1) (Nat.card_eq_fintype_card.symm.trans hc)

end Places

open GlobalTheory.MemN.TypesInhab in

theorem goodSeriesIdempotent_central_idempotent (D : D7) :
    D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) ∧ D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0 := by
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  obtain ⟨hc, hm⟩ := good_sum (I := TypePl D) (P := fun v => Fin D.R.r → ZMod (D.host.g v.1))
    (fun v p => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf p))
    (fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) D.ntypes.e0 (fun g => rfl)
    (fun _ _ => D.ntypes.eSer_idem _ _) (fun _ _ => D.ntypes.eSer_central _ _)
    (fun _ p q hpq => D.ntypes.eSer_orth _ _ _ fun h => hpq (funext fun i => by
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))
  refine ⟨hc, ?_⟩
  have h : D.ntypes.e0 = ∑ a : ∀ v : TypePl D, Fin D.R.r → ZMod (D.host.g v.1),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ten (fun v => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf (a v))) else 0 := by
    ext g
    rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    refine (finsum_eq_sum_of_fintype _).trans (Finset.sum_congr rfl fun a _ => ?_)
    split_ifs <;> rfl
  conv_lhs => rhs; rw [h]
  rw [Finset.mul_sum]
  conv_rhs => rw [h]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [hm, if_pos ha]
  · rw [mul_zero]

theorem isCentralIdempotent_of_goodSeriesIdempotent {D : D7} {LL : Type} [Field LL] (σ₀ : LL →+* ℂ) {eC : G0g D.nd → LL}
    (h : ∀ g, σ₀ (eC g) = D.ntypes.e0.coeff g) : IsCentralIdem eC := by
  obtain ⟨hc, hi⟩ := goodSeriesIdempotent_central_idempotent D
  refine ⟨fun g x => σ₀.injective ?_, fun g => σ₀.injective ?_⟩
  · have := congrArg (fun z => z.coeff (x * g))
      (Subalgebra.mem_center_iff.1 hc (MonoidAlgebra.single x (1 : ℂ)))
    simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, inv_mul_cancel_left, one_mul, mul_one] at this
    rw [h, h, this]
  · rw [map_sum, h, ← hi, GlobalTheory.MemN.TypesInhab.coeff_mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_mul, h, h]

theorem isKappa_unique {D : D7} {j : ℕ} {w w' : WeightFamilies.Wt D j} (h : IsKappa D j w) (h' : IsKappa D j w') : w = w' := by
  obtain ⟨aP, aM, _, _, n, _⟩ := w
  obtain ⟨aP', aM', _, _, n', _⟩ := w'
  obtain rfl : n = n' := h.1.trans h'.1.symm
  obtain rfl : aP = aP' := funext fun τ => funext fun i => by
    exact_mod_cast ((h.2 τ).1 i).trans ((h'.2 τ).1 i).symm
  obtain rfl : aM = aM' := funext fun τ => funext fun i => by
    have := ((h.2 τ).2 i.rev).trans ((h'.2 τ).2 i.rev).symm
    rw [Fin.rev_rev] at this
    exact_mod_cast this
  rfl

section Sides

variable {D : D7} (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
  (LL : Type) [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]

def SideA (Pe : ∀ (G : Type) [Group G] [Fintype G] (Pg : Finset (Pl D.host.E)), (G ≃* G0 Pg D.R.r) → (G → LL) → Prop) :
    Prop :=
  ∀ (WL : Type) [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 T.Q.c.F) WL]
    [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
    (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    (G : Type) [Group G] [Fintype G]
    (A : FormsL LL T.Q.c.F WL W G) (ι : Cusp T j w →ₗ[T.Q.c.F] WL), CarriesCusp T j w A ι →
  ∀ (Pg : Finset (Pl D.host.E)), IsTypeSet T Pg →
  ∀ (φ : G ≃* G0 Pg D.R.r), IsDetChar φ A.chi →
  ∀ (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) LL), IsGenericPsi Pg ψ →
  ∀ eC : G → LL, Pe G Pg φ eC →
    MjFull A (levJ φ (P0 Pg D.R.r ψ).conj) (levLam φ (P0 Pg D.R.r ψ).conj) eC

def SideB (Pe : (G0g D.nd → LL) → Prop) : Prop :=
  ∀ (WL : Type) [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 T.Q.c.F) WL]
    [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
    (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    (A : FormsL LL T.Q.c.F WL W (G0g D.nd)) (ι : T.cuspA j (wtA w) w.n →ₗ[T.Q.c.F] WL),
    IsFormsOf T j (wtA w) w.n A ι →
  ∀ (χ : ∀ v : TypePl D, (ZMod (D.host.g v.1))ˣ →* LLˣ), A.chi = chiDetG D χ →
  ∀ (ψ : ∀ v : TypePl D, AddChar (ZMod (D.host.g v.1)) LL), (∀ v, ψ v ≠ 1) →
  ∀ (eC : G0g D.nd → LL), Pe eC → MjLattice A (unipG D) (unipotentCharacterOfAddChars D ψ) eC

def ReadAt {LL : Type} (Pe : (G0g D.nd → LL) → Prop) (G : Type) [Group G] [Fintype G] (Pg : Finset (Pl D.host.E))
    (φ : G ≃* G0 Pg D.R.r) (eC : G → LL) : Prop :=
  ∃ P : PlaceIso D Pg, Pe fun g => eC (φ.symm (P.grp g))

end Sides

end GlobalTheory.GoodLatCompare
