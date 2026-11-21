import Formalism.LocalToGlobal.UnitaryNorms.UnramT
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondCommDistinctPlaces
import Formalism.LocalToGlobal.GlobalTheory.GL6.FrameTranslate
import Formalism.LocalToGlobal.GlobalTheory.GL6.EqOneOfCoprimeTorsionTwoPrimes
import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocV
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrames

section
noncomputable section

open Classical Finset

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

section Gen

theorem character_sum_nonzero_duals {k M V : Type} [Field k] [Fintype k] [DecidableEq k] [AddCommGroup M] [Module k M] [Fintype (Module.Dual k M)]
    [AddCommGroup V] [Module ℂ V] (ψ : AddChar k ℂ) (te : M) (Tg : Module.Dual k M → V)
    (hZ : ∀ g : Module.Dual k M, g ≠ 0 → ∑ a : kˣ, Tg ((a : k) • g) = 0) :
    ∑ g ∈ Finset.univ.filter (fun g : Module.Dual k M => g ≠ 0), ψ (g te) • Tg g =
      ∑ g ∈ Finset.univ.filter (fun g : Module.Dual k M => g te = 1), ∑ a : kˣ, ψ (a : k) • Tg ((a : k) • g) := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun g : Module.Dual k M => g te = 0)]
  set S0 := (Finset.univ.filter (fun g : Module.Dual k M => g ≠ 0)).filter (fun g => g te = 0) with hS0
  have hmem0 : ∀ g, g ∈ S0 ↔ g ≠ 0 ∧ g te = 0 := by
    intro g; simp [hS0]
  have hZ0 : ∑ g ∈ S0, ψ (g te) • Tg g = 0 := by
    have e1 : ∑ g ∈ S0, ψ (g te) • Tg g = ∑ g ∈ S0, Tg g := by
      refine Finset.sum_congr rfl (fun g hg => ?_)
      rw [((hmem0 g).1 hg).2, AddChar.map_zero_eq_one, one_smul]
    rw [e1]
    have e2 : ∀ a : kˣ, ∑ g ∈ S0, Tg ((a : k) • g) = ∑ g ∈ S0, Tg g := by
      intro a
      refine Finset.sum_nbij' (fun g => (a : k) • g) (fun g => ((a⁻¹ : kˣ) : k) • g) ?_ ?_ ?_ ?_ ?_
      · intro g hg
        obtain ⟨h1, h2⟩ := (hmem0 g).1 hg
        exact (hmem0 _).2 ⟨smul_ne_zero (Units.ne_zero a) h1, by simp [h2]⟩
      · intro g hg
        obtain ⟨h1, h2⟩ := (hmem0 g).1 hg
        exact (hmem0 _).2 ⟨smul_ne_zero (Units.ne_zero _) h1, by simp [h2]⟩
      · intro g _; simp [smul_smul]
      · intro g _; simp [smul_smul]
      · intro g _; rfl
    have e3 : ∑ a : kˣ, ∑ g ∈ S0, Tg ((a : k) • g) = 0 := by
      rw [Finset.sum_comm]
      exact Finset.sum_eq_zero (fun g hg => hZ g ((hmem0 g).1 hg).1)
    have e4 : ((Fintype.card kˣ : ℕ) : ℂ) • ∑ g ∈ S0, Tg g = 0 := by
      rw [Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.sum_const, ← e3]
      exact Finset.sum_congr rfl (fun a _ => (e2 a).symm)
    have hne : ((Fintype.card kˣ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have := congrArg (fun x => (((Fintype.card kˣ : ℕ) : ℂ))⁻¹ • x) e4
    simpa [smul_smul, inv_mul_cancel₀ hne] using this
  rw [hZ0, zero_add]
  rw [← Finset.sum_product' (f := fun g (a : kˣ) => ψ (a : k) • Tg ((a : k) • g))]
  symm
  refine Finset.sum_bij' (fun p _ => (p.2 : k) • p.1)
    (fun g hg => ((g te)⁻¹ • g, Units.mk0 (g te) (Finset.mem_filter.1 hg).2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have h1 : p.1 te = 1 := (Finset.mem_filter.1 (Finset.mem_product.1 hp).1).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.smul_apply, smul_eq_mul, h1, mul_one]
    exact ⟨smul_ne_zero (Units.ne_zero _) (fun h0 => by rw [h0, LinearMap.zero_apply] at h1; exact zero_ne_one h1),
      Units.ne_zero _⟩
  · intro g hg
    have h0 : g te ≠ 0 := (Finset.mem_filter.1 hg).2
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true, LinearMap.smul_apply,
      smul_eq_mul]
    exact inv_mul_cancel₀ h0
  · intro p hp
    have h1 : p.1 te = 1 := (Finset.mem_filter.1 (Finset.mem_product.1 hp).1).2
    have e : ((p.2 : k) • p.1) te = p.2 := by simp [h1]
    ext1
    · simp only [e, smul_smul, inv_mul_cancel₀ (Units.ne_zero p.2), one_smul]
    · ext; simp [e]
  · intro g hg
    have h0 : g te ≠ 0 := (Finset.mem_filter.1 hg).2
    simp [smul_smul, mul_inv_cancel₀ h0]
  · intro p hp
    have h1 : p.1 te = 1 := (Finset.mem_filter.1 (Finset.mem_product.1 hp).1).2
    simp [h1]

end Gen

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 2000000 in

def DnDilLoc (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ),
    (k : (D.mem u).A.Fv v) = a → g ≠ 0 →
    ∀ δ, IsDia (Tf.cls i hi).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 k δ →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))).1 = ((Tf.cls i hi).y c).1 * η'.1 * κ'.1 →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = ((a : (D.mem u).A.Fv v) • g) ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    δ.1⁻¹ * η.1⁻¹ * η'.1 ∈ (Tf.cls i hi).lev.U

set_option maxHeartbeats 4000000 in

theorem down_transport_diamond (Tf : FormsTied D u) (hL : DnDilLoc Tf) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (c : (D.mem u).C.cls i) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (hg : g ≠ 0)
    (a : ((D.mem u).A.Fv v)ˣ) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (hφ : φ ∈ (D.fm u).Fi i) :
    (D.fm u).dnT i v c g (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ((D.fm u).dn i v c g)) =
      (D.fm u).dnT i v c ((a : (D.mem u).A.Fv v) • g) (φ ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))) := by
  obtain ⟨f, hf, hfφ⟩ := forms_from_adelic_function Tf i hi φ hφ
  have hfA := (Submodule.mem_inf.1 hf).1
  obtain ⟨k, hk, δ, hδ⟩ := diamond_elements_exist_all Tf i hi v a
  have hb := level_places_not_bad Tf.atT v
  have hF := adelic_function_right_translate_diamond (Tf.cls i hi).lev (embT D) (Tf.atT.eV v).1 (Tf.atT.eV v).2 hb hδ hfA
  have hag : (a : (D.mem u).A.Fv v) • g ≠ 0 := smul_ne_zero (Units.ne_zero a) hg
  obtain ⟨γ, η, κ, hsup, hrel, hl1, hfun, htr⟩ := Tf.dn i hi v c g hg
  obtain ⟨γ', η', κ', hsup', hrel', hl1', hfun', htr'⟩ := Tf.dn i hi v c _ hag
  have hk0 := hL i hi v c g a k hk hg δ hδ γ η κ hsup hrel hl1 hfun γ' η' κ' hsup' hrel' hl1' hfun'
  have e1 : Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ((D.fm u).dn i v c g) =
      fun z => f ((Tf.cls i hi).y ((D.fm u).dn i v c g) * δ) ((Tf.val i hi).eY z) := by
    show (D.fm u).dilT i v a ((D.fm u).dn i v c g) (φ ((D.fm u).dil i v a ((D.fm u).dn i v c g))) = _
    rw [hfφ]
    exact (Tf.val i hi).dilT v a k hk _ δ hδ f hfA
  have h1 := htr (fun x => f (x * δ)) hF
  rw [e1, h1, hfφ, htr' f hfA]
  funext s
  have hx : ((Tf.cls i hi).y c * η').1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (1 : GL (Fin (D.R.N i)) D.host.E) *
        ((Tf.cls i hi).y c * η * δ).1 * (⟨_, hk0⟩ : (Tf.cls i hi).lev.U).1 := by
    simp only [Subgroup.coe_mul, map_one, one_mul]
    group
  have hval := adelic_value_translate (Tf.cls i hi).lev (embT D) (fun τ x => embedding_conj_compat D τ x) hfA 1
    (UJ _ _).one_mem _ _ ⟨_, hk0⟩ hx ((Tf.val i hi).eY s)
  have hχ : (Tf.cls i hi).lev.chi ⟨_, hk0⟩ = 1 := by
    apply (Tf.cls i hi).lev.chi_triv
    intro v'' hv''
    have hne : v'' ≠ (Tf.atT.eV v).1 := fun e => hb (e ▸ hv'')
    simp only [map_mul, map_inv, hδ.1 v'' hne, hsup v'' hne, hsup' v'' hne, inv_one, mul_one]
  rw [hval, hχ, Units.val_one, one_mul, rnd_tr_congr (embT D) (fun τ x => embedding_conj_compat D τ x) inv_one _ (UJ _ _).one_mem,
    rnd_tr_one]

set_option maxHeartbeats 1000000 in

theorem frobenius_eq_dual_sum (i : ℕ) (v : (D.mem u).A.vT) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (c : (D.mem u).C.cls i) :
    Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ c = ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ≠ 0),
      (D.mem u).A.psiT v (g ((D.fm u).te i v c)) • (D.fm u).dnT i v c g (φ ((D.fm u).dn i v c g)) := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.FFop
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  rfl

set_option maxHeartbeats 1000000 in

theorem frobenius_diamond_character_sum (i : ℕ) (v : (D.mem u).A.vT) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (c : (D.mem u).C.cls i) :
    Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ) c = ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ((D.fm u).te i v c) = 1),
      ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (a : (D.mem u).A.Fv v) •
        (D.fm u).dnT i v c g (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ((D.fm u).dn i v c g)) := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.Dop
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [LinearMap.comp_apply, LinearMap.proj_apply]
  unfold Formalism.MainNotions.product_first_zeroth_parts.Gs
  rw [LinearMap.sum_apply, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [LinearMap.smul_apply, Pi.smul_apply, map_smul]
  rfl

theorem sum_diamond_eq_norm (i : ℕ) (v : (D.mem u).A.vT) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (c : (D.mem u).C.cls i) :
    ∑ a : ((D.mem u).A.Fv v)ˣ, Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ c = Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v φ c := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.Nm
  rw [LinearMap.sum_apply, Finset.sum_apply]

set_option maxHeartbeats 2000000 in

theorem frobenius_eq_D_gauss_of_dilation (Tf : FormsTied D u) (hL : DnDilLoc Tf) :
    ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ = Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ) := by
  intro i hi v φ hφ
  have hφF : φ ∈ (D.fm u).Fi i := (Submodule.mem_inf.1 hφ).1
  have hN : Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v φ = 0 := by
    have h2 := (Submodule.mem_inf.1 hφ).2
    rw [Submodule.mem_iInf] at h2
    exact LinearMap.mem_ker.1 (h2 v)
  funext c
  rw [frobenius_eq_dual_sum, frobenius_diamond_character_sum]
  have hk : ∀ g ∈ Finset.univ.filter
      (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ((D.fm u).te i v c) = 1),
      ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (a : (D.mem u).A.Fv v) •
        (D.fm u).dnT i v c g (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ((D.fm u).dn i v c g)) =
      ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (a : (D.mem u).A.Fv v) •
        (D.fm u).dnT i v c ((a : (D.mem u).A.Fv v) • g) (φ ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))) := by
    intro g hg
    have hg0 : g ≠ 0 := by
      intro h0; have := (Finset.mem_filter.1 hg).2; rw [h0, LinearMap.zero_apply] at this; exact zero_ne_one this
    exact Finset.sum_congr rfl (fun a _ => by rw [down_transport_diamond Tf hL i hi v c g hg0 a φ hφF])
  rw [Finset.sum_congr rfl hk]
  have hZ : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c), g ≠ 0 →
      ∑ a : ((D.mem u).A.Fv v)ˣ,
        (D.fm u).dnT i v c ((a : (D.mem u).A.Fv v) • g) (φ ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))) = 0 := by
    intro g hg
    have e : ∀ a : ((D.mem u).A.Fv v)ˣ,
        (D.fm u).dnT i v c ((a : (D.mem u).A.Fv v) • g) (φ ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))) =
          (D.fm u).dnT i v c g (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ((D.fm u).dn i v c g)) :=
      fun a => (down_transport_diamond Tf hL i hi v c g hg a φ hφF).symm
    rw [Finset.sum_congr rfl (fun a _ => e a), ← map_sum, sum_diamond_eq_norm, hN]
    exact map_zero _
  convert character_sum_nonzero_duals ((D.mem u).A.psiT v) ((D.fm u).te i v c)
    (fun g => (D.fm u).dnT i v c g (φ ((D.fm u).dn i v c g))) hZ

section Rest

variable {D : D7} {u : D.what₂.Word}

theorem gauss_sum_preserves_ramified (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i)
    (hφ : φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i) : Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i := by
  have hE := diamond_elements_exist_all Tf
  have hφF : φ ∈ (D.fm u).Fi i := (Submodule.mem_inf.1 hφ).1
  have hN : ∀ v', Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v' φ = 0 := by
    intro v'
    have h2 := (Submodule.mem_inf.1 hφ).2
    rw [Submodule.mem_iInf] at h2
    exact LinearMap.mem_ker.1 (h2 v')
  refine Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 (fun v' => LinearMap.mem_ker.2 ?_)⟩
  · unfold Formalism.MainNotions.product_first_zeroth_parts.Gs
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (diamond_preserves_forms Tf hE i hi v a φ hφF))
  · have hc : ∀ (a : ((D.mem u).A.Fv v)ˣ) (b : ((D.mem u).A.Fv v')ˣ),
        Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' b (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ) =
          Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' b φ) := by
      intro a b
      by_cases hvv : v = v'
      · subst hvv
        exact diamond_comm_same_place Tf hE i hi v b a φ hφF
      · exact diamond_comm_distinct_places Tf hE i hi v v' hvv b a φ hφF
    have e : Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v' (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ) =
        Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v (Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v' φ) := by
      unfold Formalism.MainNotions.product_first_zeroth_parts.Nm Formalism.MainNotions.product_first_zeroth_parts.Gs
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hc b a]))
    rw [e, hN v', map_zero]


theorem class_form_smul_left (i : ℕ) (c : ℂ) (x y : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) :
    (D.fm u).ipC i (c • x) y = starRingEnd ℂ c * (D.fm u).ipC i x y := by
  unfold Formalism.BasicNotions.MemberForms.ipC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Pi.smul_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem class_form_smul_right (i : ℕ) (c : ℂ) (x y : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) :
    (D.fm u).ipC i x (c • y) = c * (D.fm u).ipC i x y := by
  unfold Formalism.BasicNotions.MemberForms.ipC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Pi.smul_apply, map_smul, smul_eq_mul]
  ring

theorem class_form_sum_left {ι : Type} (s : Finset ι) (i : ℕ) (x : ι → Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (y : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) :
    (D.fm u).ipC i (∑ a ∈ s, x a) y = ∑ a ∈ s, (D.fm u).ipC i (x a) y := by
  unfold Formalism.BasicNotions.MemberForms.ipC
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_apply, map_sum, LinearMap.sum_apply, Finset.mul_sum]

theorem class_form_sum_right {ι : Type} (s : Finset ι) (i : ℕ) (x : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (y : ι → Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) :
    (D.fm u).ipC i x (∑ a ∈ s, y a) = ∑ a ∈ s, (D.fm u).ipC i x (y a) := by
  unfold Formalism.BasicNotions.MemberForms.ipC
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_apply, map_sum, Finset.mul_sum]

theorem gauss_sum_commute_dual (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i)
    (hφ : φ ∈ (D.fm u).Fi i) :
    Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ) = Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v (Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v φ) := by
  have hE := diamond_elements_exist_all Tf
  unfold Formalism.MainNotions.product_first_zeroth_parts.Gs Formalism.MainNotions.product_first_zeroth_parts.GsD
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [diamond_comm_same_place Tf hE i hi v x⁻¹ y φ hφ, mul_comm]

set_option maxHeartbeats 2000000 in

theorem frobenius_class_form_similitude_of_hecke (Tf : FormsTied D u) (hL : DnDilLoc Tf) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (h1c : ∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i,
      (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v φ) ψ = (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v ψ))
    (hUD : ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ)
    (hDm : ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i)
    (hAdj : ∀ (a : ((D.mem u).A.Fv v)ˣ), ∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i,
      (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ) ψ = (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ)) :
    ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
      (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ) (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v ψ) =
        ((D.mem u).A.T : ℂ) ^ D.R.N i * (D.fm u).ipC i φ ψ := by
  intro φ hφ ψ hψ
  have hφF : φ ∈ (D.fm u).Fi i := (Submodule.mem_inf.1 hφ).1
  have hψF : ψ ∈ (D.fm u).Fi i := (Submodule.mem_inf.1 hψ).1
  have hGφ := gauss_sum_preserves_ramified Tf i hi v φ hφ
  have hGψ := gauss_sum_preserves_ramified Tf i hi v ψ hψ
  have hNψ : Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v ψ = 0 := by
    have h2 := (Submodule.mem_inf.1 hψ).2
    rw [Submodule.mem_iInf] at h2
    exact LinearMap.mem_ker.1 (h2 v)
  rw [frobenius_eq_D_gauss_of_dilation Tf hL i hi v φ hφ, frobenius_eq_D_gauss_of_dilation Tf hL i hi v ψ hψ,
    ← h1c _ (Submodule.mem_inf.1 (hDm _ hGφ)).1 _ (Submodule.mem_inf.1 hGψ).1, hUD _ hGφ, class_form_smul_left]
  have hadj : (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ) (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v ψ) =
      (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v ψ)) := by
    have hGψF := (Submodule.mem_inf.1 hGψ).1
    conv_lhs => rw [show Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ = ∑ a : ((D.mem u).A.Fv v)ˣ,
      (D.mem u).A.psiT v (a : (D.mem u).A.Fv v) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ by
        unfold Formalism.MainNotions.product_first_zeroth_parts.Gs; rw [LinearMap.sum_apply]; rfl]
    rw [class_form_sum_left]
    unfold Formalism.MainNotions.product_first_zeroth_parts.GsD
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [class_form_sum_right]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [class_form_smul_left, class_form_smul_right, hAdj a φ hφF _ hGψF, ← AddChar.map_neg_eq_conj]
  rw [hadj, gauss_sum_commute_dual Tf i hi v ψ hψF, gs_gsD_of_diaMul D u (DiaMul_tied Tf) i hi v ψ hψF, hNψ, sub_zero,
    class_form_smul_right]
  have hN2 := two_le_rank_of_level D i
  have e : D.R.N i = (D.R.N i - 1) + 1 := by omega
  conv_rhs => rw [e]
  simp only [map_pow, map_natCast]
  ring


end Rest

section Adj

variable {D : D7} {u : D.what₂.Word}

theorem dilation_one (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    (D.fm u).dil i v 1 c = c := by
  have h := (Tf.val i hi).dil v 1 1 (by simp) c 1 (is_diamond_one _ _ _)
  rw [mul_one] at h
  exact (Tf.cls i hi).y_bij.1 h

theorem dilation_mul (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a b : ((D.mem u).A.Fv v)ˣ)
    (c : (D.mem u).C.cls i) :
    (D.fm u).dil i v a ((D.fm u).dil i v b c) = (D.fm u).dil i v (b * a) c := by
  obtain ⟨ka, hka, δa, ha⟩ := diamond_elements_exist_all Tf i hi v a
  obtain ⟨kb, hkb, δb, hb⟩ := diamond_elements_exist_all Tf i hi v b
  have W := Tf.val i hi
  have h1 := W.dil v a ka hka ((D.fm u).dil i v b c) δa ha
  have h2 := W.dil v b kb hkb c δb hb
  have h3 := class_mul_right_of_normalises _ _ _ _ δa (fun κ hκ => diamond_conj_mem_level' _ _ _ ha ⟨κ, hκ⟩) h2
  have hab : ((kb * ka : ℤ) : (D.mem u).A.Fv v) = ((b * a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) := by
    rw [Int.cast_mul, hka, hkb, Units.val_mul]
  have h4 := W.dil v (b * a) (kb * ka) hab c (δb * δa) (is_diamond_mul_mult _ _ _ hb ha)
  have h5 : (Quotient.mk'' ((Tf.cls i hi).y c * δb * δa) : Cls (Tf.cls i hi).lev) =
      Quotient.mk'' ((Tf.cls i hi).y c * (δb * δa)) := by rw [mul_assoc]
  exact (Tf.cls i hi).y_bij.1 (h1.trans (h3.trans (h5.trans h4.symm)))

theorem dilation_bijective (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) :
    Function.Bijective ((D.fm u).dil i v a) := by
  refine Function.bijective_iff_has_inverse.2 ⟨(D.fm u).dil i v a⁻¹, fun c => ?_, fun c => ?_⟩
  · rw [dilation_mul Tf i hi v a⁻¹ a c, mul_inv_cancel, dilation_one Tf i hi v c]
  · rw [dilation_mul Tf i hi v a a⁻¹ c, inv_mul_cancel, dilation_one Tf i hi v c]

set_option maxHeartbeats 2000000 in

theorem diamond_adjoint_class_form (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ)
    (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (hφ : φ ∈ (D.fm u).Fi i) (ψ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) (hψ : ψ ∈ (D.fm u).Fi i) :
    (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ) ψ = (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ) := by
  have hE := diamond_elements_exist_all Tf
  have hM := DiaMul_tied Tf
  have hψ' := diamond_preserves_forms Tf hE i hi v a⁻¹ ψ hψ
  have hψeq : ψ = Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ) := by
    rw [← (hM i hi v ψ hψ).2 a a⁻¹, mul_inv_cancel, (hM i hi v ψ hψ).1]
  have hT := TrIso_tied Tf
  conv_lhs => rw [hψeq]
  unfold Formalism.BasicNotions.MemberForms.ipC
  have e1 : ∀ c, (D.mem u).C.wt i c * (D.fm u).ipV i c (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ c)
      (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ) c) =
      (fun c => (D.mem u).C.wt i c * (D.fm u).ipV i c (φ c) (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ c))
        ((D.fm u).dil i v a c) := by
    intro c
    have h := (hT i hi v c φ hφ _ hψ').2.2 a
    show (D.mem u).C.wt i c * (D.fm u).ipV i c ((D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c)))
      ((D.fm u).dilT i v a c (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ ((D.fm u).dil i v a c))) = _
    rw [h]
    simp only [Formalism.BasicNotions.ColumnChain.wt, (D.fm u).dil_stab]
  rw [Finset.sum_congr rfl (fun c _ => e1 c)]
  exact Equiv.sum_comp (Equiv.ofBijective _ (dilation_bijective Tf i hi v a))
    (fun c => (D.mem u).C.wt i c * (D.fm u).ipV i c (φ c) (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a⁻¹ ψ c))


end Adj


end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section DdlGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

set_option maxHeartbeats 2000000 in

theorem ddl_core (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (hδ : IsDia S v hv k δ)
    (η η' : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hη : ∀ v', v' ≠ v → bc (prV (E := E) v') η.1 = 1) (hη' : ∀ v', v' ≠ v → bc (prV (E := E) v') η'.1 = 1)
    (κ κ' : S.U) (W : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hWe : bc (prV (E := E) v) (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1) = W)
    (hL : W ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb))
    (hgW : W ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))))
    (hfW : ∀ x : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
        k • S.fT v hv ⟨W.1 *ᵥ x.1, (hgW x.1).1 x.2⟩ = S.fT v hv x) :
    δ.1⁻¹ * η.1⁻¹ * η'.1 ∈ S.U := by
  subst hWe
  have hκ := (S.U_eq _).1 κ.2
  have hκ' := (S.U_eq _).1 κ'.2
  have hWU : κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
    mul_mem (mul_mem (mul_mem (inv_mem hκ.1) (inv_mem η.2)) η'.2) hκ'.1
  have hDW : δ.1⁻¹ * (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1) ∈ S.U := by
    rw [S.U_eq]
    refine ⟨mul_mem (inv_mem δ.2) hWU, fun v' => ?_⟩
    by_cases h : v' = v
    · subst h
      rw [S.UlocAlt _ hv]
      obtain ⟨h1, h2, hg, h3⟩ := hδ
      rw [map_mul, map_inv]
      refine Subgroup.mem_inf.2 ⟨(levelVL σ J v' S.Lb).mul_mem ((levelVL σ J v' S.Lb).inv_mem h2)
        (Subgroup.mem_inf.2 ⟨Formalism.UG.P.afsplit_bc_mem _ _ _ _ hWU, hL⟩), ?_⟩
      have hgg := (stabGL _).mul_mem ((stabGL _).inv_mem hg) hgW
      refine ⟨hgg, fun x => ?_⟩
      set y : latS (F := F) (v'.adicCompletion F) (intV E v')
          (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) :=
        ⟨((bc (prV (E := E) v') δ.1)⁻¹ * bc (prV (E := E) v') (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1)).1 *ᵥ x.1,
          (hgg x.1).1 x.2⟩ with hy
      have e1 : (⟨(bc (prV (E := E) v') δ.1).1 *ᵥ y.1, (hg y.1).1 y.2⟩ :
          latS (F := F) (v'.adicCompletion F) (intV E v') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) =
          ⟨(bc (prV (E := E) v') (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1)).1 *ᵥ x.1, (hgW x.1).1 x.2⟩ := by
        apply Subtype.ext
        simp only [hy, Matrix.mulVec_mulVec, Units.val_mul, ← Matrix.mul_assoc]
        rw [Units.mul_inv, Matrix.one_mul]
      have A := h3 y
      rw [e1, hfW x] at A
      exact A.symm
    · have e : bc (prV (E := E) v') (δ.1⁻¹ * (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1)) =
          (bc (prV (E := E) v') κ.1)⁻¹ * bc (prV (E := E) v') κ'.1 := by
        simp only [map_mul, map_inv, hδ.1 v' h, hη v' h, hη' v' h, inv_one, one_mul, mul_one]
      rw [e]
      exact mul_mem (inv_mem (hκ.2 v')) (hκ'.2 v')
  have e : δ.1⁻¹ * η.1⁻¹ * η'.1 = (δ.1⁻¹ * κ.1 * δ.1) * (δ.1⁻¹ * (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1)) * κ'.1⁻¹ := by
    group
  rw [e]
  exact mul_mem (mul_mem (diamond_conj_mem_level S v hv hδ κ) hDW) (inv_mem κ'.2)

theorem ddl_comp_eq {G : Type} [Group G] (y y' y'' η κ η' κ' g g' : G)
    (h1 : g * y' = y * η * κ) (h2 : g' * y'' = y * η' * κ') :
    κ⁻¹ * η⁻¹ * η' * κ' = y'⁻¹ * (g⁻¹ * g') * y'' := by
  have e1 : η * κ = y⁻¹ * g * y' := by rw [mul_assoc y⁻¹, h1]; group
  have e2 : η' * κ' = y⁻¹ * g' * y'' := by rw [mul_assoc y⁻¹, h2]; group
  calc κ⁻¹ * η⁻¹ * η' * κ' = (η * κ)⁻¹ * (η' * κ') := by group
    _ = _ := by rw [e1, e2]; group

end DdlGen

section DdlLoc

variable {E : Type} [Field E] [NumberField E]

theorem ddl_mulLat_one {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : mulLat (1 : Matrix (Fin n) (Fin n) E) L = L := by
  ext x
  simp only [mulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.one_mulVec]
  exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem localization_inv_smul_eq {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime] (g : GL (Fin n) E) {A B : Submodule (𝓞 E) (Fin n → E)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g : Matrix (Fin n) (Fin n) E) A) = Formalism.HermitianLatticesTheory.localization₂ P B) :
    Formalism.HermitianLatticesTheory.localization₂ P (mulLat ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) B) = Formalism.HermitianLatticesTheory.localization₂ P A := by
  have k1 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.ge
  have k2 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.le
  rw [← rlv_mulLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ddl_mulLat_one] at k1 k2
  exact le_antisymm k1 k2

variable {E : Type} [Field E] [NumberField E]

theorem localization_mono₂ (P : Ideal (𝓞 E)) [P.IsPrime] {n : ℕ} {M N : Submodule (𝓞 E) (Fin n → E)} (h : M ≤ N) :
    Formalism.HermitianLatticesTheory.localization₂ P M ≤ Formalism.HermitianLatticesTheory.localization₂ P N := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (rlv_mem_locP _ _ _).1 hx
  exact (rlv_mem_locP _ _ _).2 ⟨s, hs, h hsx⟩

theorem mem_localization_of_mem₂ (P : Ideal (𝓞 E)) [P.IsPrime] {n : ℕ} {M : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (h : x ∈ M) : x ∈ Formalism.HermitianLatticesTheory.localization₂ P M :=
  (rlv_mem_locP _ _ _).2 ⟨1, P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance), by rw [one_smul]; exact h⟩

theorem localization_smul_cancel {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime] (g g' : GL (Fin n) E) {A B : Submodule (𝓞 E) (Fin n → E)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g' : Matrix (Fin n) (Fin n) E) B) = Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g : Matrix (Fin n) (Fin n) E) A)) :
    Formalism.HermitianLatticesTheory.localization₂ P (mulLat ((g⁻¹ * g' : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) B) = Formalism.HermitianLatticesTheory.localization₂ P A := by
  have k1 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.le
  have k2 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.ge
  have e1 : ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * (g : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [← rlv_mulLat_mul, ← rlv_mulLat_mul, e1, ddl_mulLat_one, ← Units.val_mul] at k1 k2
  exact le_antisymm k1 k2

end DdlLoc

section DdlTied

variable {D : D7} {u : D.what₂.Word}

def ddlW (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c1 c2 : (D.mem u).C.cls i)
    (g : GL (Fin (D.R.N i)) D.host.E) :
    GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] (Tf.atT.eV v).1.adicCompletion D.host.F) :=
  bc (prV (E := D.host.E) (Tf.atT.eV v).1) (((Tf.cls i hi).y c1).1⁻¹ *
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g * ((Tf.cls i hi).y c2).1)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def DnDilLocV (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ),
    (k : (D.mem u).A.Fv v) = a → g ≠ 0 →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))).1 = ((Tf.cls i hi).y c).1 * η'.1 * κ'.1 →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = ((a : (D.mem u).A.Fv v) • g) ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ.1⁻¹ * γ'.1).1 (clsCrd D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) =
              Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi ((D.fm u).dn i v c g)) ∧
    Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (mulLat (γ.1⁻¹ * γ'.1).1 (clsCrd D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) =
              Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (clsCrd D u i hi ((D.fm u).dn i v c g)) ∧
    ∃ hg : ddlW Tf i hi v ((D.fm u).dn i v c g) ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)) (γ.1⁻¹ * γ'.1) ∈
        stabGL (latS (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (Tf.atT.eV v).1)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (Tf.cls i hi).lev.Lb))),
      ∀ x : latS (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (Tf.atT.eV v).1)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (Tf.cls i hi).lev.Lb)),
        k • (Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2
            ⟨(ddlW Tf i hi v ((D.fm u).dn i v c g) ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)) (γ.1⁻¹ * γ'.1)).1 *ᵥ x.1,
              (hg x.1).1 x.2⟩ =
          (Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2 x

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem dnDilLoc_of_V (Tf : FormsTied D u) (h : DnDilLocV Tf) : DnDilLoc Tf := by
  intro i hi v c g a k hk hg δ hδ γ η κ hsup hrel hl hfun γ' η' κ' hsup' hrel' hl' hfun'
  obtain ⟨hP, hQ, hW, hf⟩ := h i hi v c g a k hk hg γ η κ hsup hrel hl hfun γ' η' κ' hsup' hrel' hl' hfun'
  have heq := ddl_comp_eq ((Tf.cls i hi).y c).1 ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1
    ((Tf.cls i hi).y ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))).1 η.1 κ.1 η'.1 κ'.1
    (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1)
    (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1) hrel hrel'
  rw [← map_inv, ← map_mul] at heq
  have e : bc (prV (E := D.host.E) (Tf.atT.eV v).1) (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1) =
      ddlW Tf i hi v ((D.fm u).dn i v c g) ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)) (γ.1⁻¹ * γ'.1) := by
    unfold ddlW; rw [heq]
  refine ddl_core (Tf.cls i hi).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 hδ η η' hsup hsup' κ κ' _ e ?_ hW hf
  unfold ddlW
  exact rlv_stabT Tf i hi v _ _ (γ.1⁻¹ * γ'.1) hP hQ

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem ddl_dualP (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c1 c2 : (D.mem u).C.cls i)
    (γ γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hl : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi c1)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hl' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi c2)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c)) :
    Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ.1⁻¹ * γ'.1).1 (Ld D u i hi c2)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c1) := by
  rw [Units.val_mul]
  exact rlv_chainP _ _ _ (localization_inv_smul_eq _ γ.1 hl) hl'

def LocalToGlobal₂ (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c, Lk Tf.atT i hi v c ≤ Ld D u i hi c ∧
    Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c) ≤ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem ddk_char (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c1 : (D.mem u).C.cls i)
    (hKc : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c) ≤ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hK1 : Lk Tf.atT i hi v c1 ≤ Ld D u i hi c1)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hl : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi c1)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hfun : ∀ (x : ↥(Ld D u i hi c1)) (hx : γ.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
      (D.fm u).fv i v c1 ((Tf.lv i hi).pr v c1 x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩))
    (y : Fin (D.R.N i) → D.host.E) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Lk Tf.atT i hi v c1)) ↔
      ∃ s : 𝓞 D.host.E, s ∉ Tf.atT.Pv v ∧ ∃ h : s • y ∈ Lk Tf.atT i hi v c, g ((Tf.lv i hi).prk v c ⟨_, h⟩) = 0 := by
  have hP : (Tf.atT.Pv v).IsPrime := inferInstance
  constructor
  · intro hy
    obtain ⟨s, hs, hsy⟩ := (rlv_mem_locP _ _ _).1 hy
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hsy
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hxe
    have hxd : x ∈ Ld D u i hi c1 := hK1 hx
    have hγx : γ.1.1 *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) := by
      rw [← hl]
      exact mem_localization_of_mem₂ _ (Submodule.mem_map.2 ⟨x, hxd, rfl⟩)
    obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hγx
    have hsm : γ.1.1 *ᵥ (t • x) = t • (γ.1.1 *ᵥ x) := Matrix.mulVec_smul _ _ _
    have hmem : γ.1.1 *ᵥ ((t • (⟨x, hxd⟩ : ↥(Ld D u i hi c1)) : ↥(Ld D u i hi c1)) : Fin (D.R.N i) → D.host.E) ∈
        Lk Tf.atT i hi v c := by
      show γ.1.1 *ᵥ (t • x) ∈ _
      rw [hsm]
      exact Submodule.mem_sup_left htx
    have h1 := hfun (t • ⟨x, hxd⟩) hmem
    rw [(Tf.lv i hi).pr_smul, map_smul, ((Tf.lv i hi).fv_ker v c1 ⟨x, hxd⟩).2 hx, smul_zero] at h1
    have hts : (t * s) • y ∈ Lk Tf.atT i hi v c := by
      rw [mul_smul, ← hxe]
      exact Submodule.mem_sup_left htx
    refine ⟨t * s, fun h => (hP.mem_or_mem h).elim ht hs, hts, ?_⟩
    have e : (⟨(t * s) • y, hts⟩ : ↥(Lk Tf.atT i hi v c)) = ⟨_, hmem⟩ := by
      apply Subtype.ext
      show (t * s) • y = γ.1.1 *ᵥ (t • x)
      rw [hsm, hxe, mul_smul]
    rw [e]
    exact h1.symm
  · rintro ⟨s, hs, h, h0⟩
    have h2 : s • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) := hKc (mem_localization_of_mem₂ _ h)
    obtain ⟨r, hr, hry⟩ := (rlv_mem_locP _ _ _).1 h2
    have h3 : r • s • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi c1)) := by
      rw [hl]; exact mem_localization_of_mem₂ _ hry
    obtain ⟨t, ht, hty⟩ := (rlv_mem_locP _ _ _).1 h3
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hty
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hxe
    have hmem : γ.1.1 *ᵥ (⟨x, hx⟩ : ↥(Ld D u i hi c1)).1 ∈ Lk Tf.atT i hi v c := by
      show γ.1.1 *ᵥ x ∈ _
      rw [hxe]
      exact Submodule.mem_sup_left (Submodule.smul_mem _ t hry)
    have h1 := hfun ⟨x, hx⟩ hmem
    have e : (⟨γ.1.1 *ᵥ (⟨x, hx⟩ : ↥(Ld D u i hi c1)).1, hmem⟩ : ↥(Lk Tf.atT i hi v c)) = (t * r) • ⟨s • y, h⟩ := by
      apply Subtype.ext
      show γ.1.1 *ᵥ x = (t * r) • (s • y)
      rw [hxe, mul_smul]
    rw [e, (Tf.lv i hi).prk_smul, map_smul, h0, smul_zero] at h1
    have hxk : x ∈ Lk Tf.atT i hi v c1 := ((Tf.lv i hi).fv_ker v c1 ⟨x, hx⟩).1 h1
    refine (rlv_mem_locP _ _ _).2 ⟨t * r * s, fun hh => (hP.mem_or_mem hh).elim
      (fun hh' => (hP.mem_or_mem hh').elim ht hr) hs, ?_⟩
    refine Submodule.mem_map.2 ⟨x, hxk, ?_⟩
    show γ.1.1 *ᵥ x = (t * r * s) • y
    rw [hxe, mul_smul, mul_smul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem ddk_latP (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c1 c2 : (D.mem u).C.cls i)
    (hKc : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c) ≤ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hK1 : Lk Tf.atT i hi v c1 ≤ Ld D u i hi c1) (hK2 : Lk Tf.atT i hi v c2 ≤ Ld D u i hi c2)
    (hK1' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c1) ≤ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c1))
    (hK2' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c2) ≤ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c2))
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (a : ((D.mem u).A.Fv v)ˣ)
    (γ γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hl : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi c1)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hfun : ∀ (x : ↥(Ld D u i hi c1)) (hx : γ.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
      (D.fm u).fv i v c1 ((Tf.lv i hi).pr v c1 x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩))
    (hl' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi c2)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hfun' : ∀ (x : ↥(Ld D u i hi c2)) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
      (D.fm u).fv i v c2 ((Tf.lv i hi).pr v c2 x) = ((a : (D.mem u).A.Fv v) • g) ((Tf.lv i hi).prk v c ⟨_, hx⟩)) :
    Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ.1⁻¹ * γ'.1).1 (clsCrd D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c1) := by
  have eq1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Lk Tf.atT i hi v c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Lk Tf.atT i hi v c1)) := by
    ext y
    rw [ddk_char Tf i hi v c c2 hKc hK2 _ γ' hl' hfun' y, ddk_char Tf i hi v c c1 hKc hK1 g γ hl hfun y]
    simp only [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, Units.ne_zero, false_or]
  have L1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c1) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c1) :=
    le_antisymm hK1' (localization_mono₂ _ le_sup_left)
  have L2 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c2) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c2) :=
    le_antisymm hK2' (localization_mono₂ _ le_sup_left)
  have M1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Lk Tf.atT i hi v c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi c1)) :=
    le_antisymm (rlv_locP_mulLat_le _ _ L1.le) (rlv_locP_mulLat_le _ _ L1.ge)
  have M2 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Lk Tf.atT i hi v c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (clsCrd D u i hi c2)) :=
    le_antisymm (rlv_locP_mulLat_le _ _ L2.le) (rlv_locP_mulLat_le _ _ L2.ge)
  rw [M1, M2] at eq1
  exact localization_smul_cancel _ γ.1 γ'.1 eq1

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def DnDilLocW (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ),
    (k : (D.mem u).A.Fv v) = a → g ≠ 0 →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))).1 = ((Tf.cls i hi).y c).1 * η'.1 * κ'.1 →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = ((a : (D.mem u).A.Fv v) • g) ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (mulLat (γ.1⁻¹ * γ'.1).1 (clsCrd D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) =
              Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (clsCrd D u i hi ((D.fm u).dn i v c g)) ∧
    ∃ hg : ddlW Tf i hi v ((D.fm u).dn i v c g) ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)) (γ.1⁻¹ * γ'.1) ∈
        stabGL (latS (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (Tf.atT.eV v).1)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (Tf.cls i hi).lev.Lb))),
      ∀ x : latS (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (Tf.atT.eV v).1)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (Tf.cls i hi).lev.Lb)),
        k • (Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2
            ⟨(ddlW Tf i hi v ((D.fm u).dn i v c g) ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)) (γ.1⁻¹ * γ'.1)).1 *ᵥ x.1,
              (hg x.1).1 x.2⟩ =
          (Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2 x

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem dilation_local_v_of_kernel_and_local_w (Tf : FormsTied D u) (hK : LocalToGlobal₂ Tf) (h : DnDilLocW Tf) : DnDilLocV Tf := by
  intro i hi v c g a k hk hg γ η κ hsup hrel hl hfun γ' η' κ' hsup' hrel' hl' hfun'
  exact ⟨ddk_latP Tf i hi v c _ _ (hK i hi v c).2 (hK i hi v _).1 (hK i hi v _).1 (hK i hi v _).2 (hK i hi v _).2 g a γ γ'
    hl hfun hl' hfun', h i hi v c g a k hk hg γ η κ hsup hrel hl hfun γ' η' κ' hsup' hrel' hl' hfun'⟩



end DdlTied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section DualQ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem rlv_dualQ {n : ℕ} (σ : E →ₐ[F] E) (hσσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E)
    (hH : ∀ u w, hform (σ : E →+* E) J w u = σ (hform (σ : E →+* E) J u w))
    (g : Matrix (Fin n) (Fin n) E) (hg : cT (σ : E →+* E) g * J * g = J)
    (P : Ideal (𝓞 E)) [P.IsPrime] {A B : Submodule (𝓞 E) (Fin n → E)}
    (hBfg : (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B).FG)
    (hBB : Formalism.L2.GlobalTheoryTheory.Comp.dl σ J (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B) ≤ B)
    (hP : Formalism.HermitianLatticesTheory.localization₂ P (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B) ≤ Formalism.HermitianLatticesTheory.localization₂ P (mulLat g (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J A))) :
    Formalism.HermitianLatticesTheory.localization₂ (P.comap (RingOfIntegers.mapRingHom (σ : E →+* E))) (mulLat g A) ≤
      Formalism.HermitianLatticesTheory.localization₂ (P.comap (RingOfIntegers.mapRingHom (σ : E →+* E))) B := by
  classical
  have hP1 : (1 : 𝓞 E) ∉ P := P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)
  intro x hx
  obtain ⟨t0, ht0, hx0⟩ := (rlv_mem_locP _ _ _).1 hx
  obtain ⟨a, ha, hax⟩ := Submodule.mem_map.1 hx0
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hax
  have key : ∀ y ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B, ∃ s : 𝓞 E, s ∉ P ∧
      (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := (rlv_mem_locP _ _ _).1 (hP ((rlv_mem_locP _ _ _).2 ⟨1, hP1, by rw [one_smul]; exact hy⟩))
    obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.1 hsy
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hwy
    refine ⟨s, hs, ?_⟩
    have e1 : (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y = hform (σ : E →+* E) J (g *ᵥ a) (s • y) := by
      rw [← algebraMap_smul E s y, Formalism.L2.GlobalTheoryTheory.Comp.hform_smul_right]
    rw [e1, ← hwy, Formalism.UG.P.hform_mulVec, hg]
    exact (Formalism.L2.GlobalTheoryTheory.Comp.mem_dl σ J A w).1 hw a ha
  choose! sf hsfP hsf using key
  obtain ⟨S, hS⟩ := hBfg
  have hSsub : ∀ y ∈ S, y ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B := fun y hy => hS ▸ Submodule.subset_span hy
  set s : 𝓞 E := ∏ y ∈ S, sf y with hsdef
  have hsP : s ∉ P := by
    rw [hsdef, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨y, hy, hyP⟩
    exact hsfP y (hSsub y hy) hyP
  have hgen : ∀ y ∈ S, (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    rw [hsdef, ← Finset.mul_prod_erase S sf hy]
    obtain ⟨r, hr⟩ := hsf y (hSsub y hy)
    refine ⟨(∏ z ∈ S.erase y, sf z) * r, ?_⟩
    rw [map_mul, hr]
    push_cast
    ring
  have hall : ∀ y ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B, (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hgen y hy
    | zero => rw [Formalism.L2.GlobalTheoryTheory.Comp.hform_zero_right, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Formalism.L2.GlobalTheoryTheory.Comp.hform_add_right, mul_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [← algebraMap_smul E r y, Formalism.L2.GlobalTheoryTheory.Comp.hform_smul_right]
      obtain ⟨q, hq⟩ := hy
      exact ⟨r * q, by rw [map_mul, hq]; ring⟩
  set s' : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) s with hs'def
  have hs'E : (s' : E) = σ (s : E) := rfl
  have hmem : s' • (g *ᵥ a) ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B) := by
    apply Submodule.subset_span
    intro y hy
    have e2 : hform (σ : E →+* E) J y (s' • (g *ᵥ a)) = σ ((s : E) * hform (σ : E →+* E) J (g *ᵥ a) y) := by
      rw [← algebraMap_smul E s' (g *ᵥ a), Formalism.L2.GlobalTheoryTheory.Comp.hform_smul_right, hH, map_mul]
      rfl
    rw [e2]
    obtain ⟨q, hq⟩ := hall y hy
    exact ⟨RingOfIntegers.mapRingHom (σ : E →+* E) q, by rw [← hq]; rfl⟩
  refine (rlv_mem_locP _ _ _).2 ⟨s' * t0, ?_, ?_⟩
  · intro hm
    rcases (Ideal.IsPrime.mem_or_mem inferInstance hm) with h1 | h1
    · apply hsP
      have : RingOfIntegers.mapRingHom (σ : E →+* E) s' = s := by
        apply RingOfIntegers.ext
        show σ (σ (s : E)) = (s : E)
        exact hσσ _
      rw [← this]
      exact h1
    · exact ht0 h1
  · rw [mul_smul, ← hax]
    exact hBB hmem

end DualQ

section TiedQ

variable {D : D7} {u : D.what₂.Word}

theorem rlv_sig_sig (x : D.host.E) : sigD D (sigD D x) = x := by
  rw [forms_involution_eq_host_conj, forms_involution_eq_host_conj, host_conj_involutive]

set_option maxHeartbeats 2000000 in

theorem rlv_coordFacts (i : ℕ) (hi : i ≤ D.R.m) :
    (∀ c, Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)) =
      clsCrd D u i hi c) ∧
    (∀ c, (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)).FG) ∧
    (∀ a b, hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) b a =
      sigD D (hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b)) := by
  letI := D.host.cmStar
  set κ : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) with hκ
  have hform_eq : ∀ x y, (D.sp.X i).hT x y = hform (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (κ x) (κ y) := by
    intro x y
    have hx : (D.sp.X i).hT x y = ∑ a, ∑ b, star ((D.sp.X i).frame.repr x a) * (D.sp.X i).gram a b *
        (D.sp.X i).frame.repr y b := by
      conv_lhs => rw [← (D.sp.X i).frame.sum_repr x, ← (D.sp.X i).frame.sum_repr y]
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply, HSpace.gram, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [RingHom.id_apply]
      ring
    rw [hx]
    unfold hform
    rw [← (finCongr (rankN D i hi)).symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← (finCongr (rankN D i hi)).symm.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [gramN, hκ, CMData.sig, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, starRingEnd_apply]
  let K : Formalism.L2.GlobalTheoryTheory.Comp.Coord D.sp.cm (D.sp.X i) (Fin (D.R.N i)) := ⟨κ, gramN D i hi, hform_eq⟩
  refine ⟨fun c => ?_, fun c => ?_, fun a b => ?_⟩
  · have h1 := Formalism.HermitianLatticesTheory.dualLattice (𝓞 D.host.E) D.host.E (D.sp.X i).V (D.sp.X i).hT (D.sp.X i).herm (D.sp.X i).nondeg
      Formalism.L2.GlobalTheoryTheory.Comp.star_int (D.clsLat u i c) (D.clsLat_lat u i c)
    have e1 := K.lat_dual (Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c))
    have e2 := K.lat_dual (D.clsLat u i c)
    rw [h1.2.1, e2] at e1
    exact e1.symm
  · have h1 := Formalism.HermitianLatticesTheory.dualLattice (𝓞 D.host.E) D.host.E (D.sp.X i).V (D.sp.X i).hT (D.sp.X i).herm (D.sp.X i).nondeg
      Formalism.L2.GlobalTheoryTheory.Comp.star_int (D.clsLat u i c) (D.clsLat_lat u i c)
    have e2 := K.lat_dual (D.clsLat u i c)
    have h3 := K.isLat_lat h1.1
    rw [e2] at h3
    exact Module.Finite.iff_fg.1 h3.1
  · have h := (D.sp.X i).herm.eq (κ.symm a) (κ.symm b)
    rw [hform_eq, hform_eq, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm

set_option maxHeartbeats 2000000 in

theorem rlv_Q_of_dualP (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c2 : (D.mem u).C.cls i)
    (g : GL (Fin (D.R.N i)) D.host.E) (hgU : g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hPd : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (g : Matrix _ _ D.host.E) (Ld D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c)) :
    Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (mulLat (g : Matrix _ _ D.host.E) (clsCrd D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (clsCrd D u i hi c) := by
  obtain ⟨hdd, hfg, hH⟩ := rlv_coordFacts (D := D) (u := u) i hi
  have hgU' : g⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) := inv_mem hgU
  have hg1 : cT (sigD D : D.host.E →+* D.host.E) (g : Matrix _ _ D.host.E) * gramN D i hi * (g : Matrix _ _ D.host.E) =
      gramN D i hi := hgU
  have hg1' : cT (sigD D : D.host.E →+* D.host.E) ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) * gramN D i hi *
      ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) = gramN D i hi := hgU'
  have hPd' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)) ≤
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (g : Matrix _ _ D.host.E)
        (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c2))) := hPd.ge
  have hPd'' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (g : Matrix _ _ D.host.E)
        (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c2))) ≤
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)) := hPd.le
  apply le_antisymm
  · exact rlv_dualQ (sigD D) rlv_sig_sig (gramN D i hi) hH _ hg1 (Tf.atT.Pv v) (hfg c) (hdd c).le hPd'
  · have h1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c2)) ≤
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E)
          (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c))) := by
      have := rlv_locP_mulLat_le (Tf.atT.Pv v) ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) hPd''
      rwa [rlv_mulLat_inv] at this
    have h2 := rlv_dualQ (sigD D) rlv_sig_sig (gramN D i hi) hH _ hg1' (Tf.atT.Pv v) (hfg c2) (hdd c2).le h1
    have h3 := rlv_locP_mulLat_le (rlvQ Tf.atT v) (g : Matrix _ _ D.host.E) h2
    have e3 := rlv_mulLat_inv g⁻¹ (clsCrd D u i hi c)
    rw [inv_inv] at e3
    rw [e3] at h3
    exact h3

end TiedQ

section TiedW

variable {D : D7} {u : D.what₂.Word}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def RUpLocW (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c ((Tf.lv i hi).pr v c z) = 1 →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c) →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = (D.fm u).fv i v c ((Tf.lv i hi).pr v c ⟨_, hx⟩)) →
    ∃ e : (D.fm u).lk i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lv i v c,
      e ((D.fm u).te i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) = (Tf.lv i hi).pr v c z ∧
      ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
          ((Tf.cls i hi).y ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap))).1 =
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 * η'.1 * κ'.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap))))
          (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) =
            (((D.fm u).fv i v c).comp e.toLinearMap)
              ((Tf.lv i hi).prk v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) ⟨_, hx⟩)) →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ.1 * γ'.1).1 (clsCrd D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap)))) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) ∧
      bc (prV (E := D.host.E) (Tf.atT.eV v).1) (((Tf.cls i hi).y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ.1 * γ'.1) *
        ((Tf.cls i hi).y ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap))).1) ∈ stabFun _ ((Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def RDnLocW (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ((D.fm u).te i v c) = 1 →
    ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
          ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η'.1 * κ'.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    ∃ e : (D.fm u).lv i v ((D.fm u).dn i v c g) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lk i v c,
      (D.fm u).fv i v ((D.fm u).dn i v c g) = g.comp e.toLinearMap ∧
      ∀ (z : ↥(Ld D u i hi ((D.fm u).dn i v c g))),
        (Tf.lv i hi).pr v ((D.fm u).dn i v c g) z = e.symm ((D.fm u).te i v c) →
      ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))).1 =
          ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 * η.1 * κ.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v)
                  (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi ((D.fm u).dn i v c g)) →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v)
                  (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi ((D.fm u).dn i v c g) ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi ((D.fm u).dn i v c g)),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) =
            (D.fm u).fv i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v ((D.fm u).dn i v c g) ⟨_, hx⟩)) →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ'.1 * γ.1).1 (Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c) ∧
      bc (prV (E := D.host.E) (Tf.atT.eV v).1) (((Tf.cls i hi).y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ'.1 * γ.1) *
        ((Tf.cls i hi).y ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))).1) ∈ stabFun _ ((Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem raising_local_v_of_local_w (Tf : FormsTied D u) (h : RUpLocW Tf) : RUpLocV Tf := by
  intro i hi v c z hz γ η κ hsup hrel hl1 hl2 hfun
  obtain ⟨e, he1, he2⟩ := h i hi v c z hz γ η κ hsup hrel hl1 hl2 hfun
  refine ⟨e, he1, fun γ' η' κ' hsup' hrel' hl1' hfun' => ?_⟩
  obtain ⟨hP, hF⟩ := he2 γ' η' κ' hsup' hrel' hl1' hfun'
  exact ⟨hP, rlv_Q_of_dualP Tf i hi v c _ (γ.1 * γ'.1) (mul_mem γ.2 γ'.2)
    (rlv_upDn_dualP Tf i hi v c _ _ γ γ' hl1 hl1'), hF⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem lowering_local_v_of_local_w (Tf : FormsTied D u) (h : RDnLocW Tf) : RDnLocV Tf := by
  intro i hi v c g hg γ' η' κ' hsup' hrel' hl1' hfun'
  obtain ⟨e, he1, he2⟩ := h i hi v c g hg γ' η' κ' hsup' hrel' hl1' hfun'
  refine ⟨e, he1, fun z hz γ η κ hsup hrel hl1 hl2 hfun => ?_⟩
  obtain ⟨hPd, hF⟩ := he2 z hz γ η κ hsup hrel hl1 hl2 hfun
  exact ⟨rlv_dnUp_latP Tf i hi v c _ _ γ' γ hl1' hl1,
    rlv_Q_of_dualP Tf i hi v c _ (γ'.1 * γ.1) (mul_mem γ'.2 γ.2) hPd, hF⟩



end TiedW

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

section
noncomputable section

open NumberField Ideal IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms

section Unr

variable {D : D7} {u : D.what₂.Word}

theorem unramified_algebraic_weights (A : AtTTied u) (v : (D.mem u).A.vT) :
    ∃ s : 𝓞 D.host.E, s ∉ A.Pv v ∧
      ∀ x ∈ A.Pv v, ∃ z : 𝓞 D.host.E, x * s = z * (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have : CharP ((D.mem u).A.Fv v) (D.mem u).A.T := charP_of_card_eq_prime ((D.mem u).A.card_Fv v)
  have hPmax : (A.Pv v).IsMaximal := RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)
  have hres_nat : ∀ s : ℕ, A.res v (s : 𝓞 D.host.E) = 0 ↔ (D.mem u).A.T ∣ s := by
    intro s; rw [map_natCast]; exact CharP.cast_eq_zero_iff _ (D.mem u).A.T s
  have := Formalism.L2.Host.span_isPrime (D.mem u).A.T
  have hlies : (A.Pv v).LiesOver (span {((D.mem u).A.T : ℤ)}) := by
    refine ⟨?_⟩
    have hle : span {((D.mem u).A.T : ℤ)} ≤ (A.Pv v).comap (algebraMap ℤ (𝓞 D.host.E)) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show A.res v (algebraMap ℤ (𝓞 D.host.E) ((D.mem u).A.T : ℤ)) = 0
      rw [map_natCast]
      exact (hres_nat _).2 dvd_rfl
    have hmax : (span {((D.mem u).A.T : ℤ)}).IsMaximal := by
      refine this.isMaximal ?_
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (D.mem u).A.T_prime.ne_zero
    exact hmax.eq_of_le (Ideal.comap_ne_top _ hPmax.ne_top) hle
  obtain ⟨I, hI, hIP⟩ := Formalism.L2.Host.map_eq_mul_coprime D.host (D.mem u).A.T (Formalism.L2.Host.T_ne A v) (A.Pv v)
  obtain ⟨s, hsI, hsP⟩ := Set.not_subset.mp hIP
  refine ⟨s, hsP, fun x hx => ?_⟩
  have hxs : x * s ∈ (span {((D.mem u).A.T : ℤ)}).map (algebraMap ℤ (𝓞 D.host.E)) := by
    rw [hI]; exact Ideal.mul_mem_mul hx hsI
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', map_natCast] at hxs
  obtain ⟨z, hz⟩ := hxs
  exact ⟨z, hz.symm⟩

theorem unr_smul (A : AtTTied u) (v : (D.mem u).A.vT) :
    ∃ s : 𝓞 D.host.E, s ∉ A.Pv v ∧ ∀ {W : Type} [AddCommGroup W] [Module (𝓞 D.host.E) W]
      (M : Submodule (𝓞 D.host.E) W), ∀ x ∈ A.Pv v • M,
        ∃ y ∈ M, s • x = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y := by
  obtain ⟨s, hs, h⟩ := unramified_algebraic_weights A v
  refine ⟨s, hs, fun {W} _ _ M x hx => ?_⟩
  refine Submodule.smul_induction_on (p := fun x => ∃ y ∈ M, s • x = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y) hx
    (fun p hp m hm => ?_) (fun x1 x2 h1 h2 => ?_)
  · obtain ⟨z, hz⟩ := h p hp
    exact ⟨z • m, M.smul_mem z hm, by rw [smul_smul, smul_smul, mul_comm s p, hz, mul_comm z]⟩
  · obtain ⟨a, ha, ea⟩ := h1
    obtain ⟨b, hb, eb⟩ := h2
    exact ⟨a + b, M.add_mem ha hb, by rw [smul_add, ea, eb, smul_add]⟩

theorem exists_smul_eq_smul_of_mem_ideal_smul {W : Type} [AddCommGroup W] [Module (𝓞 D.host.E) W] (A : AtTTied u) (v : (D.mem u).A.vT)
    (M : Submodule (𝓞 D.host.E) W) (x : W) (hx : x ∈ A.Pv v • M) :
    ∃ s : 𝓞 D.host.E, s ∉ A.Pv v ∧ ∃ y ∈ M, s • x = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y := by
  obtain ⟨s, hs, h⟩ := unr_smul A v
  obtain ⟨y, hy, e⟩ := h M x hx
  exact ⟨s, hs, y, hy, e⟩


end Unr

section TLd

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 2000000 in

theorem tld_isLat (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Formalism.L2.GlobalTheoryTheory.Comp.IsLat (clsCrd D u i hi c) := by
  letI := D.host.cmStar
  set κ : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) with hκ
  have hform_eq : ∀ x y, (D.sp.X i).hT x y = Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (κ x) (κ y) := by
    intro x y
    have hx : (D.sp.X i).hT x y = ∑ a, ∑ b, star ((D.sp.X i).frame.repr x a) * (D.sp.X i).gram a b *
        (D.sp.X i).frame.repr y b := by
      conv_lhs => rw [← (D.sp.X i).frame.sum_repr x, ← (D.sp.X i).frame.sum_repr y]
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply, HSpace.gram, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [RingHom.id_apply]
      ring
    rw [hx]
    unfold Formalism.UG.hform
    rw [← (finCongr (rankN D i hi)).symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← (finCongr (rankN D i hi)).symm.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [gramN, hκ, CMData.sig, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, starRingEnd_apply]
  let K : Formalism.L2.GlobalTheoryTheory.Comp.Coord D.sp.cm (D.sp.X i) (Fin (D.R.N i)) := ⟨κ, gramN D i hi, hform_eq⟩
  exact K.isLat_lat (D.clsLat_lat u i c)

end TLd

section TLdLoc

open Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word}

end TLdLoc

section SFGen

open Matrix Formalism.UG IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sf_mulVec_smul {n : ℕ} (v : HeightOneSpectrum (𝓞 F))
    (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (s : intV E v)
    (w : Fin n → E ⊗[F] v.adicCompletion F) : M *ᵥ (s • w) = s • (M *ᵥ w) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ * ((s : E ⊗[F] v.adicCompletion F) * w j) = (s : E ⊗[F] v.adicCompletion F) * (_ * w j)
  ring

set_option maxHeartbeats 1000000 in

theorem sf_of_gen {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (L2 Lb : Submodule (𝓞 E) (Fin n → E))
    {Mm : Type} [AddCommGroup Mm] [Module (intV E v) Mm]
    (f : latS (F := F) (v.adicCompletion F) (intV E v) Lb →ₗ[intV E v] Mm)
    (y2 : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy2 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 ↔
      ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb)
    (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb))
    (hgen : ∀ z ∈ L2, ∀ h1 : ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun i => inclE (F := F) (v.adicCompletion F) (z i)) ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb,
      f ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun i => inclE (F := F) (v.adicCompletion F) (z i))), (hg _).1 h1⟩ = f ⟨_, h1⟩) :
    g ∈ stabFun (latS (F := F) (v.adicCompletion F) (intV E v) Lb) f := by
  refine ⟨hg, fun x => ?_⟩
  have key : ∀ w (hw : w ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2),
      f ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ w),
        (hg _).1 ((hy2 w).1 hw)⟩ = f ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ w, (hy2 w).1 hw⟩ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨z, hz, rfl⟩ := hw
      exact hgen z hz _
    | zero =>
      have e1 : (⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ 0),
          (hg _).1 ((hy2 0).1 (zero_mem _))⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) = 0 :=
        Subtype.ext (by simp)
      have e2 : (⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ 0, (hy2 0).1 (zero_mem _)⟩ :
          latS (F := F) (v.adicCompletion F) (intV E v) Lb) = 0 :=
        Subtype.ext (by simp)
      rw [e1, e2]
    | add a b ha hb iha ihb =>
      have e1 : (⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (a + b)),
          (hg _).1 ((hy2 _).1 (add_mem ha hb))⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
          ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ a), (hg _).1 ((hy2 a).1 ha)⟩ +
          ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ b), (hg _).1 ((hy2 b).1 hb)⟩ :=
        Subtype.ext (by simp only [Submodule.coe_add, Matrix.mulVec_add])
      have e2 : (⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (a + b), (hy2 _).1 (add_mem ha hb)⟩ :
          latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
          ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ a, (hy2 a).1 ha⟩ +
          ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ b, (hy2 b).1 hb⟩ :=
        Subtype.ext (by simp only [Submodule.coe_add, Matrix.mulVec_add])
      rw [e1, e2, map_add, map_add, iha, ihb]
    | smul s a ha iha =>
      have e1 : (⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (s • a)),
          (hg _).1 ((hy2 _).1 (Submodule.smul_mem _ s ha))⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
          s • ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ a), (hg _).1 ((hy2 a).1 ha)⟩ :=
        Subtype.ext (by simp only [Submodule.coe_smul]; rw [sf_mulVec_smul, sf_mulVec_smul])
      have e2 : (⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (s • a), (hy2 _).1 (Submodule.smul_mem _ s ha)⟩ :
          latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
          s • ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ a, (hy2 a).1 ha⟩ :=
        Subtype.ext (by simp only [Submodule.coe_smul]; rw [sf_mulVec_smul])
      rw [e1, e2, map_smul, map_smul, iha]
  have e : ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ ((y2 : Matrix (Fin n) (Fin n) _) *ᵥ x.1) = x.1 := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hx : (y2 : Matrix (Fin n) (Fin n) _) *ᵥ x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 :=
    (hy2 _).2 (by rw [e]; exact x.2)
  have h := key _ hx
  have e1 : (⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ x.1, (hg x.1).1 x.2⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) =
      ⟨(g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        ((y2 : Matrix (Fin n) (Fin n) _) *ᵥ x.1)), (hg _).1 ((hy2 _).1 hx)⟩ := Subtype.ext (by simp only [e])
  have e2 : x = ⟨((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ ((y2 : Matrix (Fin n) (Fin n) _) *ᵥ x.1),
      (hy2 _).1 hx⟩ := Subtype.ext e.symm
  rw [e1, h, ← e2]

end SFGen

section SFGen2

open Matrix Formalism.UG IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sf_bc_eq {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (y1 y2 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (g : GL (Fin n) E) :
    ((bc (prV (E := E) v) (y1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g * y2) : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _) =
      (((bc (prV (E := E) v) y1)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *
        ((g : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F))) *
        ((bc (prV (E := E) v) y2 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
  rfl

set_option maxHeartbeats 2000000 in

theorem sf_two {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (L1 L2 Lb : Submodule (𝓞 E) (Fin n → E))
    {Mm : Type} [AddCommGroup Mm] [Module (intV E v) Mm]
    (f : latS (F := F) (v.adicCompletion F) (intV E v) Lb →ₗ[intV E v] Mm)
    (y1 y2 : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy1 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L1 ↔
      ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb)
    (hy2 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 ↔
      ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb)
    (Γ : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hgM : (g : Matrix (Fin n) (Fin n) _) = ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *
      Γ.map (inclE (F := F) (v.adicCompletion F)) * (y2 : Matrix (Fin n) (Fin n) _))
    (hg : g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb))
    (hF : ∀ z ∈ L2, ∃ a : 𝓞 F, a ∉ v.asIdeal ∧ (algebraMap (𝓞 F) (𝓞 E) a) • (Γ *ᵥ z) ∈ L1 ∧
      ∀ (h1 : ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • (Γ *ᵥ z)) k)) ∈
          latS (F := F) (v.adicCompletion F) (intV E v) Lb)
        (h2 : ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • z) k)) ∈
          latS (F := F) (v.adicCompletion F) (intV E v) Lb),
        f ⟨_, h1⟩ = f ⟨_, h2⟩) :
    g ∈ stabFun (latS (F := F) (v.adicCompletion F) (intV E v) Lb) f := by
  refine sf_of_gen v L2 Lb f y2 hy2 g hg ?_
  intro z hz h1
  have eG : (g : Matrix (Fin n) (Fin n) _) *ᵥ (((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun k => inclE (F := F) (v.adicCompletion F) (z k))) =
      ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun k => inclE (F := F) (v.adicCompletion F) ((Γ *ᵥ z) k)) := by
    rw [hgM, mulVec_mulVec, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one,
      ← mulVec_mulVec]
    congr 1
    funext k
    exact (RingHom.map_mulVec _ _ _ k).symm
  obtain ⟨a, ha, hΓ, hfa⟩ := hF z hz
  let t : intV E v := ⟨(1 : E) ⊗ₜ[F] ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletionIntegers F) :
      v.adicCompletion F), Subring.subset_closure (Or.inr ⟨⟨_, (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a).2⟩, rfl⟩)⟩
  have hι : ∀ y : Fin n → E, (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • y) k)) =
      t • (fun k => inclE (F := F) (v.adicCompletion F) (y k)) := by
    intro y; funext k
    show inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) a) • y k) =
      (t : E ⊗[F] v.adicCompletion F) * inclE (F := F) (v.adicCompletion F) (y k)
    rw [rlv_incl_smul, mul_comm]; rfl
  have hA' : ((y1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • (Γ *ᵥ z)) k)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) Lb := (hy1 _).1 (Submodule.subset_span ⟨_, hΓ, rfl⟩)
  have hB' : ((y2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun k => inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) a) • z) k)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) Lb := (hy2 _).1 (Submodule.subset_span ⟨_, Submodule.smul_mem _ _ hz, rfl⟩)
  have hfT := hfa hA' hB'
  have eA : (⟨_, hA'⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) = t • ⟨_, (hg _).1 h1⟩ := Subtype.ext (by
    simp only [Submodule.coe_smul]
    rw [hι, sf_mulVec_smul, eG])
  have eB : (⟨_, hB'⟩ : latS (F := F) (v.adicCompletion F) (intV E v) Lb) = t • ⟨_, h1⟩ := Subtype.ext (by
    simp only [Submodule.coe_smul]
    rw [hι, sf_mulVec_smul])
  rw [eA, eB, map_smul, map_smul] at hfT
  obtain ⟨s, hs, hsr⟩ := rlv_unit (E := E) v a ha
  have hst1 : (⟨s, hs⟩ : intV E v) * t = 1 := Subtype.ext hsr
  have := congrArg (fun m => (⟨s, hs⟩ : intV E v) • m) hfT
  simp only [smul_smul, hst1, one_smul] at this
  exact this

end SFGen2

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end
