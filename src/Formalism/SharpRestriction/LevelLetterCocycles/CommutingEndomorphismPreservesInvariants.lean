import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.PadicSubsetSums.StableGradedCounts.TWCutOperator
import Formalism.PadicSubsetSums.StableGradedCounts.TWExportTransfer
import Formalism.PadicSubsetSums.StableGradedCounts.TWLengthBaseChange
import Formalism.SharpRestriction.LevelLetterCocycles.GaloisEquivariantKeyFunction

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section Comm

variable {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W] [Module R W]

theorem sIdx_eq (l : ℕ) (M N : Submodule R W) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l M N =
      (Formalism.IrreducibleCountingLemmas.TW.sIdx M N : ℝ) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ) := by
  unfold Formalism.MainNotions.IntegralHeckeForms.sIdx Formalism.MainNotions.IntegralHeckeForms.lenR Formalism.IrreducibleCountingLemmas.TW.sIdx Formalism.IrreducibleCountingLemmas.TW.relLen
  push_cast
  rw [sub_div]

theorem length_ne_top_of_smul_eq_zero {X : Type} [AddCommGroup X] [Module R X] [Module.Finite R X]
    (c : R) (hc : c ≠ 0) (h : ∀ x : X, c • x = 0) : Module.length R X ≠ ⊤ := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R X
  let li : Fin n → (R ⧸ Ideal.span {c}) →ₗ[R] X := fun i =>
    Submodule.liftQ (Ideal.span {c}) (LinearMap.toSpanSingleton R X (f (Pi.single i 1))) (by
      rw [Ideal.span, Submodule.span_le]
      rintro _ rfl
      simp [h])
  let g : (Fin n → R ⧸ Ideal.span {c}) →ₗ[R] X := ∑ i, (li i) ∘ₗ LinearMap.proj i
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨v, rfl⟩ := hf x
    refine ⟨fun i => Submodule.Quotient.mk (v i), ?_⟩
    have hv : v = ∑ i, v i • (Pi.single i (1 : R) : Fin n → R) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    simp only [g, li, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    erw [Submodule.liftQ_apply]
    simp
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective g hg)
  rw [Module.length_pi]
  have h1 : Module.length R (R ⧸ Ideal.span {c}) ≠ ⊤ := Formalism.IrreducibleCountingLemmas.TW.Idx.ord_ne_top' hc
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 h1
  rw [← ha, ENat.card_eq_coe_fintype_card]
  exact_mod_cast ENat.natCast_ne_top _

theorem exists_smul_le {M N V : Submodule R W} (hM : IsLatIn M V) (hN : IsLatIn N V) :
    ∃ c : R, c ≠ 0 ∧ ∀ x ∈ M, c • x ∈ N := by
  classical
  obtain ⟨S, hS⟩ := hM.1
  have hSV : ∀ s ∈ S, s ∈ V := fun s hs => hM.2.1 (hS ▸ Submodule.subset_span hs)
  choose! c hc0 hcN using fun s (hs : s ∈ S) => hN.2.2 s (hSV s hs)
  refine ⟨∏ s ∈ S, c s, Finset.prod_ne_zero_iff.2 hc0, ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem s hs =>
    rw [← Finset.mul_prod_erase S c hs, mul_comm, mul_smul]
    exact N.smul_mem _ (hcN s hs)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact N.smul_mem _ hx

theorem relLen_ne_top {M N V : Submodule R W} (hM : IsLatIn M V) (hN : IsLatIn N V) :
    relLen M N ≠ ⊤ := by
  obtain ⟨c, hc, h⟩ := exists_smul_le hM hN
  have : Module.Finite R M := Module.Finite.iff_fg.2 hM.1
  unfold relLen
  refine length_ne_top_of_smul_eq_zero c hc ?_
  intro x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact h m m.2

theorem isLatIn_inf {M N V : Submodule R W} (hM : IsLatIn M V) (hN : IsLatIn N V) :
    IsLatIn (M ⊓ N) V := by
  refine ⟨?_, inf_le_left.trans hM.2.1, ?_⟩
  · have : IsNoetherian R M := isNoetherian_of_fg_of_noetherian M hM.1
    have h2 : ((M ⊓ N).comap M.subtype).FG := IsNoetherian.noetherian _
    have h3 := h2.map M.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 inf_le_left] at h3
  · intro x hx
    obtain ⟨c, hc, h⟩ := hM.2.2 x hx
    obtain ⟨c', hc', h'⟩ := hN.2.2 x hx
    refine ⟨c * c', mul_ne_zero hc hc', ?_, ?_⟩
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h
    · rw [mul_smul]; exact N.smul_mem _ h'

theorem sIdx_eq_sub {M N Q V : Submodule R W} (hM : IsLatIn M V) (hN : IsLatIn N V)
    (hQ : IsLatIn Q V) (hQM : Q ≤ M) (hQN : Q ≤ N) :
    Formalism.IrreducibleCountingLemmas.TW.sIdx M N = ((relLen M Q).toNat : ℤ) - ((relLen N Q).toNat : ℤ) := by
  have h1 := Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_tower (le_inf hQM hQN) (inf_le_left : M ⊓ N ≤ M)
  have h2 := Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_tower (le_inf hQM hQN) (inf_le_right : M ⊓ N ≤ N)
  rw [Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_inf] at h1
  rw [inf_comm, Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_inf] at h2
  have f0 := relLen_ne_top (isLatIn_inf hN hM) hQ
  have f1 := relLen_ne_top hM hN
  have f2 := relLen_ne_top hN hM
  rw [inf_comm] at h1
  unfold Formalism.IrreducibleCountingLemmas.TW.sIdx
  rw [h1, h2, ENat.toNat_add f0 f1, ENat.toNat_add f0 f2]
  push_cast
  ring

theorem sIdx_add {M N P V : Submodule R W} (hM : IsLatIn M V) (hN : IsLatIn N V) (hP : IsLatIn P V) :
    Formalism.IrreducibleCountingLemmas.TW.sIdx M N + Formalism.IrreducibleCountingLemmas.TW.sIdx N P = Formalism.IrreducibleCountingLemmas.TW.sIdx M P := by
  have hQ := isLatIn_inf (isLatIn_inf hM hN) hP
  have q1 : M ⊓ N ⊓ P ≤ M := inf_le_left.trans inf_le_left
  have q2 : M ⊓ N ⊓ P ≤ N := inf_le_left.trans inf_le_right
  have q3 : M ⊓ N ⊓ P ≤ P := inf_le_right
  rw [sIdx_eq_sub hM hN hQ q1 q2, sIdx_eq_sub hN hP hQ q2 q3, sIdx_eq_sub hM hP hQ q1 q3]
  ring

theorem sIdx_diff (l : ℕ) {M M' N N' V : Submodule R W} (hM : IsLatIn M V) (hM' : IsLatIn M' V)
    (hN : IsLatIn N V) (hN' : IsLatIn N' V) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l M N' - Formalism.MainNotions.IntegralHeckeForms.sIdx l M N =
      Formalism.MainNotions.IntegralHeckeForms.sIdx l M' N' - Formalism.MainNotions.IntegralHeckeForms.sIdx l M' N := by
  have a := sIdx_add hM hN hN'
  have b := sIdx_add hM' hN hN'
  have c : Formalism.IrreducibleCountingLemmas.TW.sIdx M N' - Formalism.IrreducibleCountingLemmas.TW.sIdx M N =
      Formalism.IrreducibleCountingLemmas.TW.sIdx M' N' - Formalism.IrreducibleCountingLemmas.TW.sIdx M' N := by omega
  simp only [sIdx_eq, ← sub_div]
  congr 1
  exact_mod_cast c

end Comm

end Idx

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section BaseChange

variable {R R' W W' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
  [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W'] [Module R' W'] [IsScalarTower R R' W']

def ext (R' : Type) {R W W' : Type} [CommRing R] [CommRing R'] [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] [Module R' W'] (ι : W →ₗ[R] W') (N : Submodule R W) :
    Submodule R' W' :=
  Submodule.span R' (ι '' N)

theorem relLen_sup {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (M N : Submodule R W) :
    relLen M N = relLen (M ⊔ N) N := by
  rw [← Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_inf]
  unfold relLen
  exact (LinearMap.quotientInfEquivSupQuotient M N).length_eq

variable {ι : W →ₗ[R] W'}

theorem ext_sup (M N : Submodule R W) : ext R' ι (M ⊔ N) = ext R' ι M ⊔ ext R' ι N := by
  apply le_antisymm
  · unfold ext
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨m, hm, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨n, hn, rfl⟩))
  · exact sup_le (Submodule.span_mono (Set.image_mono (le_sup_left (a := M) (b := N))))
      (Submodule.span_mono (Set.image_mono (le_sup_right (a := M) (b := N))))

variable (hι : IsBaseChange R' ι)

def th (P : Submodule R W) : R' ⊗[R] P →ₗ[R'] W' :=
  hι.equiv.toLinearMap ∘ₗ P.subtype.baseChange R'

theorem th_tmul (P : Submodule R W) (a : R') (p : P) : th hι P (a ⊗ₜ p) = a • ι p := by
  simp [th, IsBaseChange.equiv_tmul]

theorem range_th (P : Submodule R W) : LinearMap.range (th hι P) = ext R' ι P := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a p =>
      rw [th_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, p.2, rfl⟩)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · unfold ext
    rw [Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨1 ⊗ₜ ⟨p, hp⟩, by rw [th_tmul, one_smul]⟩

theorem th_injective [Module.Flat R R'] (P : Submodule R W) : Function.Injective (th hι P) := by
  refine hι.equiv.injective.comp ?_
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := R') P.subtype P.injective_subtype

include hι in
theorem relLen_ext_of_le [Module.Flat R R'] {N P : Submodule R W} (h : N ≤ P) :
    relLen (ext R' ι P) (ext R' ι N) = Module.length R' (R' ⊗[R] (P ⧸ N.comap P.subtype)) := by
  set N₀ := N.comap P.subtype with hN₀
  let φ : R' ⊗[R] P →ₗ[R'] (ext R' ι P ⧸ (ext R' ι N).comap (ext R' ι P).subtype) :=
    (Submodule.mkQ _) ∘ₗ (LinearMap.codRestrict (ext R' ι P) (th hι P)
      (fun t => range_th hι P ▸ ⟨t, rfl⟩))
  let ψ : R' ⊗[R] P →ₗ[R'] R' ⊗[R] (P ⧸ N₀) := N₀.mkQ.baseChange R'
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← range_th hι P] at hy
    obtain ⟨t, rfl⟩ := hy
    exact ⟨t, rfl⟩
  have hψ : Function.Surjective ψ := by
    show Function.Surjective (N₀.mkQ.baseChange R')
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
  have kψ : ∀ t, ψ t = 0 ↔ t ∈ LinearMap.range (N₀.subtype.baseChange R') := by
    intro t
    have := lTensor_exact R' (LinearMap.exact_subtype_mkQ N₀) (Submodule.mkQ_surjective N₀) t
    exact this
  have kφ : ∀ t, φ t = 0 ↔ t ∈ LinearMap.range (N₀.subtype.baseChange R') := by
    intro t
    have h0 : φ t = 0 ↔ th hι P t ∈ ext R' ι N := by
      show Submodule.Quotient.mk _ = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      rfl
    rw [h0]
    constructor
    · intro ht
      have hle : ext R' ι N ≤ (LinearMap.range (N₀.subtype.baseChange R')).map (th hι P) := by
        unfold ext
        rw [Submodule.span_le]
        rintro _ ⟨n, hn, rfl⟩
        refine ⟨1 ⊗ₜ ⟨n, h hn⟩, ⟨1 ⊗ₜ ⟨⟨n, h hn⟩, hn⟩, ?_⟩, ?_⟩
        · simp
        · rw [th_tmul, one_smul]
      obtain ⟨s, hs, hst⟩ := hle ht
      rwa [← th_injective hι P hst]
    · rintro ⟨s, rfl⟩
      clear h0
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a n =>
        rw [LinearMap.baseChange_tmul, th_tmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, n.2, rfl⟩)
      | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  have hk : LinearMap.ker φ = LinearMap.ker ψ := by
    ext t
    rw [LinearMap.mem_ker, LinearMap.mem_ker, kφ, kψ]
  unfold relLen
  exact ((φ.quotKerEquivOfSurjective hφ).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (ψ.quotKerEquivOfSurjective hψ))).length_eq

theorem exists_ram (hinj : Function.Injective (algebraMap R R')) [Algebra.IsIntegral R R'] :
    ∃ (ϖ : R) (ϖ' : R') (u : R'ˣ) (e : ℕ), Irreducible ϖ ∧ Irreducible ϖ' ∧
      algebraMap R R' ϖ = (u : R') * ϖ' ^ e ∧ 0 < e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible R'
  have hne : algebraMap R R' ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hϖ.ne_zero
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ'
  refine ⟨ϖ, ϖ', u, e, hϖ, hϖ', hu, ?_⟩
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exfalso
    have : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').mpr hinj
    have hl : IsLocalHom (algebraMap R R') := inferInstance
    refine hϖ.not_isUnit (hl.map_nonunit ϖ ?_)
    rw [hu, pow_zero, mul_one]
    exact u.isUnit
  · exact he

variable {ϖ : R} {ϖ' : R'} {u : R'ˣ} {e : ℕ}

theorem addVal_map (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (hu : algebraMap R R' ϖ = (u : R') * ϖ' ^ e) (x : R) :
    (IsDiscreteValuationRing.addVal R' (algebraMap R R' x)).toNat =
      e * (IsDiscreteValuationRing.addVal R x).toNat := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [IsDiscreteValuationRing.addVal_def _ v hϖ n rfl,
      IsDiscreteValuationRing.addVal_def _ (Units.map (algebraMap R R').toMonoidHom v * u ^ n) hϖ' (e * n)
        (by rw [map_mul, map_pow, hu]; push_cast; simp only [Units.coe_map, MonoidHom.coe_coe,
              RingHom.toMonoidHom_eq_coe]; ring)]
    simp

include hι in
theorem relLen_ext (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (hu : algebraMap R R' ϖ = (u : R') * ϖ' ^ e) (he : 0 < e) [Module.Flat R R']
    {M N : Submodule R W} (hfin : relLen M N ≠ ⊤) :
    relLen (ext R' ι M) (ext R' ι N) = (e : ℕ∞) * relLen M N := by
  rw [relLen_sup, ← ext_sup, relLen_ext_of_le hι le_sup_right, relLen_sup M N]
  rw [relLen_sup] at hfin
  exact Formalism.IrreducibleCountingLemmas.TW.length_base_change_dvr R R' ϖ ϖ' u e hϖ hϖ' hu he _ hfin

include hι in

theorem sIdx_ext (hinj : Function.Injective (algebraMap R R')) [Algebra.IsIntegral R R'] (l : ℕ)
    {M N : Submodule R W} (h1 : relLen M N ≠ ⊤) (h2 : relLen N M ≠ ⊤) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l (ext R' ι M) (ext R' ι N) = Formalism.MainNotions.IntegralHeckeForms.sIdx l M N := by
  obtain ⟨ϖ, ϖ', u, e, hϖ, hϖ', hu, he⟩ := exists_ram (R := R) (R' := R') hinj
  have : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').mpr hinj
  have : Module.IsTorsionFree R R' := inferInstance
  have : Module.Flat R R' := inferInstance
  rw [sIdx_eq, sIdx_eq]
  unfold Formalism.IrreducibleCountingLemmas.TW.sIdx
  rw [relLen_ext hι hϖ hϖ' hu he h1, relLen_ext hι hϖ hϖ' hu he h2, ← map_natCast (algebraMap R R') l,
    addVal_map hϖ hϖ' hu, ENat.toNat_mul, ENat.toNat_mul, ENat.toNat_natCast]
  push_cast
  rw [← mul_sub, mul_div_mul_left _ _ (by exact_mod_cast he.ne')]

end BaseChange

end Idx

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section Transfer

theorem ext_span {R R' W W' : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] [Module R' W'] [IsScalarTower R R' W'] (ι : W →ₗ[R] W') (s : Set W) :
    ext R' ι (Submodule.span R s) = Submodule.span R' (ι '' s) := by
  apply le_antisymm
  · unfold ext
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [map_smul, ← algebraMap_smul R' a (ι x)]
      exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem baseChange_eq_ext {R W : Type} (A : Type) [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup W]
    [Module R W] (N : Submodule R W) : N.baseChange A = ext A (TensorProduct.mk R A W 1) N := by
  rw [Submodule.baseChange_eq_span]
  rfl

theorem isLatIn_ext {R R' W W' : Type} [CommRing R] [CommRing R'] [IsDomain R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] [Module R' W'] [IsScalarTower R R' W'] (ι : W →ₗ[R] W')
    {N V : Submodule R W} (h : IsLatIn N V) : IsLatIn (ext R' ι N) (ext R' ι V) := by
  refine ⟨?_, Submodule.span_mono (Set.image_mono h.2.1), ?_⟩
  · obtain ⟨S, hS⟩ := h.1
    rw [← hS, ext_span]
    exact Submodule.fg_span (S.finite_toSet.image _)
  · intro x hx
    unfold ext at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      obtain ⟨c, hc, hcv⟩ := h.2.2 v hv
      refine ⟨algebraMap R R' c, by rwa [Ne, map_eq_zero_iff _ hinj], ?_⟩
      rw [algebraMap_smul, ← map_smul]
      exact Submodule.subset_span ⟨_, hcv, rfl⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, h1⟩ := hx
      obtain ⟨c', hc', h2⟩ := hy
      refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ h1
      · rw [mul_smul]; exact Submodule.smul_mem _ _ h2
    | smul a x _ hx =>
      obtain ⟨c, hc, h1⟩ := hx
      exact ⟨c, hc, by rw [smul_comm]; exact Submodule.smul_mem _ _ h1⟩

variable {O Ok O' Fm : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing Ok] [IsDomain Ok] [IsDiscreteValuationRing Ok] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] [Algebra O Ok] [Algebra Ok O'] [Algebra O O'] [IsScalarTower O Ok O']
  [AddCommGroup Fm] [Module O Fm]

variable (O Ok O' Fm) in

def gk : Ok ⊗[O] Fm →ₗ[Ok] O' ⊗[O] Fm :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap Ok O') LinearMap.id

theorem gk_apply (t : Ok ⊗[O] Fm) :
    gk O Ok O' Fm t = LinearMap.rTensor Fm (IsScalarTower.toAlgHom O Ok O').toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a f => simp [gk]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem gk_comp : (gk O Ok O' Fm).restrictScalars O ∘ₗ TensorProduct.mk O Ok Fm 1 =
    TensorProduct.mk O O' Fm 1 := by
  ext f
  simp [gk]

theorem gk_isBaseChange : IsBaseChange O' (gk O Ok O' Fm) := by
  refine IsBaseChange.of_comp (TensorProduct.isBaseChange O Fm Ok) ?_
  have := TensorProduct.isBaseChange O Fm O'
  rw [← gk_comp (Ok := Ok)] at this
  exact this

theorem ext_gk (N : Submodule O Fm) : ext O' (gk O Ok O' Fm) (N.baseChange Ok) = N.baseChange O' := by
  rw [Submodule.baseChange_eq_span, ext_span, Submodule.baseChange_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n, hn, (LinearMap.congr_fun (gk_comp (O := O) (Ok := Ok) (O' := O') (Fm := Fm)) n).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨_, ⟨n, hn, rfl⟩, LinearMap.congr_fun (gk_comp (O := O) (Ok := Ok) (O' := O') (Fm := Fm)) n⟩

theorem transfer (h1 : Function.Injective (algebraMap O Ok)) [Module.Finite O Ok]
    (h2 : Function.Injective (algebraMap Ok O')) [Module.Finite Ok O'] (l : ℕ)
    {B T V : Submodule O Fm} {Tψ : Submodule Ok (Ok ⊗[O] Fm)} (hB : IsLatIn B V) (hT : IsLatIn T V)
    (hTψ : IsLatIn Tψ (V.baseChange Ok)) (e : ℝ)
    (h : Formalism.MainNotions.IntegralHeckeForms.sIdx l (B.baseChange Ok) Tψ ≤ Formalism.MainNotions.IntegralHeckeForms.sIdx l B T + e)
    {M : Submodule O' (O' ⊗[O] Fm)} (hM : IsLatIn M (V.baseChange O')) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l M (Submodule.span O'
              ((LinearMap.rTensor Fm (IsScalarTower.toAlgHom O Ok O').toLinearMap) '' (Tψ : Set (Ok ⊗[O] Fm)))) ≤
      Formalism.MainNotions.IntegralHeckeForms.sIdx l M (T.baseChange O') + e := by
  have h3 : Function.Injective (algebraMap O O') := by
    rw [IsScalarTower.algebraMap_eq O Ok O']
    exact h2.comp h1
  have : Module.Finite O O' := Module.Finite.trans Ok O'
  have hT1 : Submodule.span O'
      ((LinearMap.rTensor Fm (IsScalarTower.toAlgHom O Ok O').toLinearMap) '' (Tψ : Set (Ok ⊗[O] Fm))) =
      ext O' (gk O Ok O' Fm) Tψ := by
    unfold ext
    rw [Set.image_congr fun t _ => (gk_apply (O' := O') t).symm]
  rw [hT1]
  have lB' : IsLatIn (B.baseChange O') (V.baseChange O') := by
    rw [baseChange_eq_ext, baseChange_eq_ext]; exact isLatIn_ext h3 _ hB
  have lT2 : IsLatIn (T.baseChange O') (V.baseChange O') := by
    rw [baseChange_eq_ext, baseChange_eq_ext]; exact isLatIn_ext h3 _ hT
  have lBk : IsLatIn (B.baseChange Ok) (V.baseChange Ok) := by
    rw [baseChange_eq_ext, baseChange_eq_ext]; exact isLatIn_ext h1 _ hB
  have lT1 : IsLatIn (ext O' (gk O Ok O' Fm) Tψ) (V.baseChange O') := by
    rw [← ext_gk (Ok := Ok) V]; exact isLatIn_ext h2 _ hTψ
  have d := sIdx_diff l hM lB' lT2 lT1
  have e1 : Formalism.MainNotions.IntegralHeckeForms.sIdx l (B.baseChange O') (T.baseChange O') = Formalism.MainNotions.IntegralHeckeForms.sIdx l B T := by
    rw [baseChange_eq_ext, baseChange_eq_ext]
    exact sIdx_ext (TensorProduct.isBaseChange O Fm O') h3 l (relLen_ne_top hB hT) (relLen_ne_top hT hB)
  have e2 : Formalism.MainNotions.IntegralHeckeForms.sIdx l (B.baseChange O') (ext O' (gk O Ok O' Fm) Tψ) =
      Formalism.MainNotions.IntegralHeckeForms.sIdx l (B.baseChange Ok) Tψ := by
    rw [← ext_gk (Ok := Ok) B]
    exact sIdx_ext gk_isBaseChange h2 l (relLen_ne_top lBk hTψ) (relLen_ne_top hTψ lBk)
  rw [e1, e2] at d
  linarith

end Transfer

end Idx

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section More

variable {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W] [Module R W]

theorem isLatIn_of_le {Y T V : Submodule R W} (hY : IsLatIn Y V) (hfg : T.FG) (hYT : Y ≤ T) (hTV : T ≤ V) :
    IsLatIn T V :=
  ⟨hfg, hTV, fun x hx => let ⟨c, hc, h⟩ := hY.2.2 x hx; ⟨c, hc, hYT h⟩⟩


theorem isLatIn_smul {N V : Submodule R W} (hN : IsLatIn N V) {c : R} (hc : c ≠ 0) :
    IsLatIn (N.map (c • (LinearMap.id : W →ₗ[R] W))) V := by
  refine ⟨hN.1.map _, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact V.smul_mem _ (hN.2.1 hx)
  · intro x hx
    obtain ⟨c', hc', h⟩ := hN.2.2 x hx
    refine ⟨c * c', mul_ne_zero hc hc', ⟨c' • x, h, ?_⟩⟩
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, mul_smul]



end More

end Idx

instance neZero_g (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

instance finite_levelGroup (N : NData D.R D.host D.what₂) : Finite (G0g N) := by
  unfold G0g
  infer_instance

theorem natCard_codeWordStages_finiteGroup_eq (N : NData D.R D.host D.what₂) : Nat.card (G0g N) = D.what₂.restRowsFiniteGroupCard := by
  unfold G0g
  rw [Nat.card_pi, Fintype.prod_sigma, N.restN_card_levelGroup_eq]
  refine Finset.prod_congr rfl fun k _ => ?_
  show ∏ _y : N.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) = _
  rw [Finset.prod_const, Finset.card_univ, N.card_PlG]

def repG (i : X.Tw) (j : ℕ) (b : Bool) : Representation (FractionRing (X.O i)) (G0g N) (Y.Fm i j b) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b)

theorem repG_apply (i : X.Tw) (j : ℕ) (b : Bool) (g : G0g N) (x : Y.Fm i j b) :
    repG Y i j b g x = Y.actG i j b g x := rfl

theorem eG_eq (i : X.Tw) (j : ℕ) (b : Bool) : eG Y i j b = (repG Y i j b).asAlgebraHom (Y.eAlg i b) := rfl

theorem eAlg_integral (i : X.Tw) (b : Bool) [CharZero (FractionRing (X.O i))] :
    ∃ c : MonoidAlgebra (X.O i) (G0g N),
      MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom c =
        ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b := by
  classical
  let _ : Fintype (G0g N) := Fintype.ofFinite _
  have hcard : Fintype.card (G0g N) = D.what₂.restRowsFiniteGroupCard := by
    rw [← Nat.card_eq_fintype_card, natCard_codeWordStages_finiteGroup_eq]
  have hint : ∀ g : G0g N, ∃ o : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) o =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) * (Y.eAlg i b).coeff g := by
    intro g
    have h := Formalism.IrreducibleCountingLemmas.TW.central_idempotent_integral_twist (FractionRing (X.O i)) (G0g N) (Y.eAlg i b)
      (Y.eAlg_idem i b) (Y.eAlg_central i b) g
    rw [hcard] at h
    have hO : IsIntegral (X.O i) (((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) * (Y.eAlg i b).coeff g) := by
      obtain ⟨p, hp, he⟩ := h
      refine ⟨p.map (Int.castRingHom (X.O i)), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      exact (congrArg (fun f => Polynomial.eval₂ f _ p) (RingHom.ext_int _ _)).trans he
    exact IsIntegrallyClosed.isIntegral_iff.1 hO
  choose o ho using hint
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm o), ?_⟩
  ext g
  simp [MonoidAlgebra.coeff_map, ho]

theorem eG_idem (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    eG Y i j b (eG Y i j b x) = eG Y i j b x := by
  rw [eG_eq, ← Module.End.mul_apply, ← map_mul, Y.eAlg_idem]

theorem eG_comm (i : X.Tw) (j : ℕ) (b : Bool) (g : G0g N) (x : Y.Fm i j b) :
    Y.actG i j b g (eG Y i j b x) = eG Y i j b (Y.actG i j b g x) := by
  rw [← repG_apply, ← repG_apply, eG_eq, ← Representation.asAlgebraHom_single_one (repG Y i j b) g,
    ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, Y.eAlg_central]

theorem eG_mem (i : X.Tw) (j : ℕ) (b : Bool) (W : Submodule (FractionRing (X.O i)) (Y.Fm i j b))
    (hW : GStable Y i j b W) (x : Y.Fm i j b) (hx : x ∈ W) : eG Y i j b x ∈ W := by
  rw [eG_eq, Formalism.IrreducibleCountingLemmas.TW.asAlgebraHom_apply_eq_sum]
  exact Submodule.sum_mem _ fun g _ => W.smul_mem _ (hW g x hx)

theorem eG_irred (i : X.Tw) (j : ℕ) (b : Bool) (W : Submodule (FractionRing (X.O i)) (Y.Fm i j b))
    (hW : GIrred Y i j b W) : (∀ x ∈ W, eG Y i j b x = x) ∨ (∀ x ∈ W, eG Y i j b x = 0) := by
  obtain ⟨_, hst, hirr⟩ := hW
  have hle : W.map (eG Y i j b) ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact eG_mem Y i j b W hst x hx
  have hst' : GStable Y i j b (W.map (eG Y i j b)) := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨Y.actG i j b g x, hst g x hx, (eG_comm Y i j b g x).symm⟩
  rcases hirr _ hle hst' with h | h
  · right
    intro x hx
    have : eG Y i j b x ∈ W.map (eG Y i j b) := ⟨x, hx, rfl⟩
    rw [h] at this
    exact (Submodule.mem_bot _).1 this
  · left
    intro x hx
    rw [← h] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact eG_idem Y i j b y

def HeckeCommutesLevelGroup : Prop :=
  ∀ (i : X.Tw), X.NonzeroIndexPlace i → ∀ (b : Bool), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ g k P, HkIdx i k P →
    (Y.actG i j b g).toLinearMap ∘ₗ Y.hkF i j b k P = Y.hkF i j b k P ∘ₗ (Y.actG i j b g).toLinearMap

theorem admissibleGoodIdempotent_iff_reduced [∀ i : X.Tw, CharZero (FractionRing (X.O i))] : GroupAlgebraIntegrality Y ↔ HeckeCommutesLevelGroup Y := by
  constructor
  · intro h i hi b j hj
    exact ((h i hi b).2 j hj).1
  · intro h i hi b
    exact ⟨eAlg_integral Y i b, fun j hj => ⟨h i hi b j hj, fun _ W _ hW => eG_irred Y i j b W hW⟩⟩

theorem mem_typeSubspace_iff_unipotent_character {i : X.Tw} {j : ℕ} {b : Bool} (x : Y.Fm i j b) :
    x ∈ Fm0 Y i j b ↔ ∀ u : Y.U, Y.actG i j b u x =
      ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • x := by
  unfold Fm0
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe]



theorem AO_apply (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    AO Y i j b x = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • eG Y i j b x := by
  show ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eG Y i j b x = _
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]



theorem card_ne_zero (i : X.Tw) [CharZero (FractionRing (X.O i))] :
    ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) ≠ 0 :=
  Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'



theorem commuting_endomorphism_preserves_forms (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (hT : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) {x : Y.Fm i j b}
    (hx : x ∈ Fm0 Y i j b) : T x ∈ Fm0 Y i j b := by
  rw [mem_typeSubspace_iff_unipotent_character] at hx ⊢
  intro u
  have := LinearMap.congr_fun (hT u) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
  rw [this, hx u, map_smul]


def expFam (i : X.Tw) (c : Bool → MonoidAlgebra (X.O i) (G0g N))
    (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)) : RFam Y i where
  Ball := fun j b => Mall Y i j b
  z := fun _ b => c b
  B := fun j b => Mall Y i j b ⊓ (V0 Y i j b).restrictScalars (X.O i)
  S := S

section Lat

open Formalism.IrreducibleCountingLemmas




theorem sIdx_eq {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W]
    [Module R W] (l : ℕ) (M N' : Submodule R W) :
    sIdx l M N' = (TW.sIdx M N' : ℝ) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ) := by
  unfold sIdx lenR TW.sIdx TW.relLen
  push_cast
  rw [sub_div]

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {U : Type} [AddCommGroup U]
  [Module R U]

abbrev LocV (V : Submodule R U) : Type := LocalizedModule (nonZeroDivisors R) ↥V

def toLoc (V : Submodule R U) : ↥V →ₗ[R] LocV V := LocalizedModule.mkLinearMap (nonZeroDivisors R) ↥V

instance isLoc_toLoc (V : Submodule R U) : IsLocalizedModule (nonZeroDivisors R) (toLoc V) :=
  inferInstanceAs (IsLocalizedModule (nonZeroDivisors R)
    (LocalizedModule.mkLinearMap (nonZeroDivisors R) ↥V))


def inLoc (V M : Submodule R U) : Submodule R (LocV V) := (M.comap V.subtype).map (toLoc V)







end Lat

section BC

open Formalism.IrreducibleCountingLemmas

theorem full_span {R U : Type*} [CommRing R] [IsDomain R] [AddCommGroup U] [Module R U]
    (N' : Submodule R U) (s : Set U) (hs : ∀ x ∈ s, ∃ c : R, c ≠ 0 ∧ c • x ∈ N') :
    ∀ x ∈ Submodule.span R s, ∃ c : R, c ≠ 0 ∧ c • x ∈ N' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact hs x h
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add]
    refine N'.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N'.smul_mem d hcx
    · rw [mul_smul]; exact N'.smul_mem c hdy
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    exact ⟨c, hc, by rw [smul_comm]; exact N'.smul_mem a hcx⟩




variable {O : Type} [CommRing O] [IsDomain O] {W : Type} [AddCommGroup W] [Module O W]
  [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W]


theorem tf_tensor {O' : Type} [CommRing O'] [IsDomain O'] [Algebra O O'] [Algebra.IsIntegral O O']
    (r : O') (x : O' ⊗[O] W) (hr : r ≠ 0) (h : r • x = 0) : x = 0 := by
  obtain ⟨d, hd, r', hr'⟩ := (Algebra.IsIntegral.isIntegral (R := O) r).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hr)
  have h1 : d • x = 0 := by
    rw [← algebraMap_smul O' d x, hr', mul_comm, mul_smul, h, smul_zero]
  have hd' : algebraMap O (FractionRing O) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hd
  let g : W →ₗ[O] W :=
    ((algebraMap O (FractionRing O) d)⁻¹ • (LinearMap.id : W →ₗ[FractionRing O] W)).restrictScalars O
  have hg : d • g = LinearMap.id := by
    ext w
    show d • ((algebraMap O (FractionRing O) d)⁻¹ • w) = w
    rw [← algebraMap_smul (FractionRing O) d, smul_smul, mul_inv_cancel₀ hd', one_smul]
  have : x = g.lTensor O' (d • x) := by
    rw [map_smul, ← LinearMap.smul_apply, ← LinearMap.lTensor_smul, hg, LinearMap.lTensor_id,
      LinearMap.id_apply]
  rw [this, h1, map_zero]

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
theorem baseChange_mono' (O' : Type) [CommRing O'] [Algebra O O'] {P V : Submodule O W} (h : P ≤ V) :
    P.baseChange O' ≤ V.baseChange O' := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact Submodule.tmul_mem_baseChange_of_mem 1 (h hx)

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
theorem map_baseChange_le (O' : Type) [CommRing O'] [Algebra O O'] {P V : Submodule O W}
    (f : W →ₗ[O] W) (h : P.map f ≤ V) : (P.baseChange O').map (f.baseChange O') ≤ V.baseChange O' := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span_le]
  rintro _ ⟨x, hx, rfl⟩
  rw [TensorProduct.mk_apply, LinearMap.baseChange_tmul]
  exact Submodule.tmul_mem_baseChange_of_mem 1 (h ⟨x, hx, rfl⟩)

omit [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
theorem isLatIn_baseChange (O' : Type) [CommRing O'] [IsDomain O'] [Algebra O O']
    (hinj : Function.Injective (algebraMap O O')) (P V : Submodule O W) (h : IsLatIn P V) :
    IsLatIn (P.baseChange O') (V.baseChange O') := by
  obtain ⟨⟨t, ht⟩, hle, hfull⟩ := h
  refine ⟨?_, baseChange_mono' O' hle, ?_⟩
  · rw [← ht, Submodule.baseChange_span]
    exact Submodule.fg_span (t.finite_toSet.image _)
  · rw [Submodule.baseChange_eq_span O' V]
    apply full_span
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨c, hc, hcv⟩ := hfull v hv
    refine ⟨algebraMap O O' c, (map_ne_zero_iff _ hinj).2 hc, ?_⟩
    rw [TensorProduct.mk_apply, algebraMap_smul, ← TensorProduct.tmul_smul]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hcv

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
theorem scaleLat_baseChange (O' : Type) [CommRing O'] [Algebra O O'] (c : O) (P : Submodule O W) :
    (TW.scaleLat c P).baseChange O' = TW.scaleLat (algebraMap O O' c) (P.baseChange O') := by
  unfold TW.scaleLat
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(1 : O') ⊗ₜ[O] x, ⟨x, hx, rfl⟩, ?_⟩
    simp
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨c • x, ⟨x, hx, rfl⟩, ?_⟩
    simp

variable {Ok O' : Type} [CommRing Ok] [CommRing O'] [Algebra O Ok] [Algebra O O'] [Algebra Ok O']
  [IsScalarTower O Ok O']

variable (O W Ok O') in

abbrev rho : Ok ⊗[O] W →ₗ[O] O' ⊗[O] W :=
  LinearMap.rTensor W (IsScalarTower.toAlgHom O Ok O').toLinearMap

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
theorem rho_smul (a : Ok) (x : Ok ⊗[O] W) :
    rho O W Ok O' (a • x) = algebraMap Ok O' a • rho O W Ok O' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b w => simp [TensorProduct.smul_tmul', Algebra.smul_def]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable (O') in

def up (T : Submodule Ok (Ok ⊗[O] W)) : Submodule O' (O' ⊗[O] W) :=
  Submodule.span O' (rho O W Ok O' '' (T : Set (Ok ⊗[O] W)))

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
theorem up_span (t : Set (Ok ⊗[O] W)) :
    up O' (Submodule.span Ok t) = Submodule.span O' (rho O W Ok O' '' t) := by
  apply le_antisymm
  · unfold up
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [rho_smul]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
theorem up_mono {T T' : Submodule Ok (Ok ⊗[O] W)} (h : T ≤ T') : up O' T ≤ up O' T' :=
  Submodule.span_mono (Set.image_mono h)

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
theorem up_baseChange (P : Submodule O W) : up O' (P.baseChange Ok) = P.baseChange O' := by
  rw [Submodule.baseChange_eq_span, up_span, Submodule.baseChange_eq_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(1 : Ok) ⊗ₜ[O] x, ⟨x, hx, rfl⟩, by simp⟩

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
theorem up_scaleLat (a : Ok) (T : Submodule Ok (Ok ⊗[O] W)) :
    up O' (TW.scaleLat a T) = TW.scaleLat (algebraMap Ok O' a) (up O' T) := by
  unfold TW.scaleLat up
  rw [Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨rho O W Ok O' x, ⟨x, hx, rfl⟩, by simp [rho_smul]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a • x, ⟨x, hx, rfl⟩, by simp [rho_smul]⟩

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
theorem isLatIn_up [IsDomain O'] (hinj : Function.Injective (algebraMap Ok O'))
    (T : Submodule Ok (Ok ⊗[O] W)) (V : Submodule O W) (h : IsLatIn T (V.baseChange Ok)) :
    IsLatIn (up O' T) (V.baseChange O') := by
  obtain ⟨⟨t, ht⟩, hle, hfull⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← ht, up_span]
    exact Submodule.fg_span (t.finite_toSet.image _)
  · rw [← up_baseChange (Ok := Ok) (O' := O') V]
    exact up_mono hle
  · rw [Submodule.baseChange_eq_span O' V]
    apply full_span
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨c, hc, hcv⟩ := hfull ((1 : Ok) ⊗ₜ[O] v) (Submodule.tmul_mem_baseChange_of_mem 1 hv)
    refine ⟨algebraMap Ok O' c, (map_ne_zero_iff _ hinj).2 hc, ?_⟩
    have : algebraMap Ok O' c • (TensorProduct.mk O O' W 1) v = rho O W Ok O' (c • (1 : Ok) ⊗ₜ[O] v) := by
      rw [rho_smul]; simp
    rw [this]
    exact Submodule.subset_span ⟨_, hcv, rfl⟩

end BC

section Tw

open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt PsiOk)

theorem psiAt_comp {Γ Γ' A : Type} [Group Γ] [Group Γ'] [CommGroup A] (b : Bool) (χ : Γ' →* A)
    (f : Γ →* Γ') : psiAt b (χ.comp f) = (psiAt b χ).comp f := by
  cases b <;> rfl

theorem TwOK_inv {i : X.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ}
    (h : TwOK i k Q ψ) : TwOK i k Q ψ⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hk : (ψ⁻¹).ker = ψ.ker := by
    ext g
    simp [MonoidHom.mem_ker]
  refine ⟨h1, h2, by rw [hk]; exact h3, ?_, ?_, ?_, ?_⟩
  · intro g g' hg
    simp only [MonoidHom.inv_apply]
    rw [h4 g g' hg]
  · intro g
    rw [MonoidHom.inv_apply]
    exact Subgroup.inv_mem _ (h5 g)
  · intro v A hA
    rw [← h6 v A hA]
    simp
  · intro v hv A' hA' σ hσ
    rw [MonoidHom.inv_apply, h7 v hv A' hA' σ hσ, inv_one]

theorem TwOK_psiAt {i : X.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ}
    (b : Bool) (h : TwOK i k Q ψ) : TwOK i k Q (psiAt b ψ) := by
  cases b
  · exact TwOK_inv h
  · exact h

theorem TwOK_of_PsiOk {i : X.Tw} {A Q : Finset (PlE D.host)} {k' : ℕ} {ψ' : X.RCG i Q →* (X.Ok i k')ˣ}
    (h : PsiOk i A Q k' ψ') : TwOK i k' Q (ψ'.comp (X.art i Q)) := by
  classical
  obtain ⟨h1, h2, _, h4, h5, h6, h7, h8⟩ := h
  exact ⟨fun P hP => (h1 P hP).1, (Finset.disjoint_union_right.1 h2).1, h4, h5, h6, h7, h8⟩


end Tw

theorem addVal_l_pos (i : X.Tw) (k : ℕ) [CharZero (FractionRing (X.O i))] :
    0 < (IsDiscreteValuationRing.addVal (X.Ok i k) ((X.l i : ℕ) : X.Ok i k)).toNat := by
  have hinj := X.Ok_inj i k
  have : Module.Finite (X.O i) (X.Ok i k) := X.Ok_fin i k
  have h0 : ((X.l i : ℕ) : X.O i) ≠ 0 := by
    intro h
    apply (Nat.cast_ne_zero (R := FractionRing (X.O i))).2 (X.lPrime i).out.ne_zero
    rw [← map_natCast (algebraMap (X.O i) (FractionRing (X.O i))), h, map_zero]
  have hne : ((X.l i : ℕ) : X.Ok i k) ≠ 0 := by
    rw [← map_natCast (algebraMap (X.O i) (X.Ok i k))]
    exact (map_ne_zero_iff _ hinj).2 h0
  have hnu : ¬ IsUnit ((X.l i : ℕ) : X.Ok i k) := by
    have : FaithfulSMul (X.O i) (X.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    have hl : IsLocalHom (algebraMap (X.O i) (X.Ok i k)) := inferInstance
    intro hu
    rw [← map_natCast (algebraMap (X.O i) (X.Ok i k))] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1 (X.O_l i) (hl.map_nonunit _ hu)
  have h1 : IsDiscreteValuationRing.addVal (X.Ok i k) ((X.l i : ℕ) : X.Ok i k) ≠ 0 :=
    fun h => hnu (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
  have h2 : IsDiscreteValuationRing.addVal (X.Ok i k) ((X.l i : ℕ) : X.Ok i k) ≠ ⊤ :=
    fun h => hne (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h2
  rw [← hn] at h1 ⊢
  rw [ENat.toNat_natCast]
  exact Nat.pos_of_ne_zero (by exact_mod_cast h1)

theorem theta_le_integral_forms (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b))
    (hSg : Sg ⊆ E.Dat0 i j b) : Th Y i j b Sg ≤ (Fm0 Y i j b).restrictScalars (X.O i) := by
  unfold Th
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  exact (mem_typeSubspace_iff_unipotent_character Y _).2 (E.theta_base_equivariant i j b a (hSg ha))











instance charZero_K (D : Formalism.BasicNotions.D7) (i : D.ntw.Tw) : CharZero (FractionRing (D.ntw.O i)) :=
  (D.nth.iC i).charZero

theorem idempotent_scaled_integral (D : Formalism.BasicNotions.D7) (i : D.ntw.Tw) (b : Bool) :
    ∃ c : MonoidAlgebra (D.ntw.O i) (G0g D.nd),
      MonoidAlgebra.map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).toAddMonoidHom c =
        ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (D.ntw.O i)) • D.nexp.eAlg i b :=
  eAlg_integral D.nexp i b


def HeckeCommutation (D : Formalism.BasicNotions.D7) : Prop := HeckeCommutesLevelGroup D.nexp



end Formalism.MainNotions.IntegralHeckeForms

end
