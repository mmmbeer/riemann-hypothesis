import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

section
noncomputable section

namespace Formalism.MainNotions.J

open Finset Matrix

section Pattern

variable {n : ℕ} {F : Type} [Field F]

def Pat (S : Finset (Fin n × Fin n)) (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, (i, j) ∉ S → A i j = if i = j then 1 else 0

theorem pat_det (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) (A : Matrix (Fin n) (Fin n) F)
    (h : Pat S A) : A.det = 1 := by
  have ht : A.BlockTriangular id := by
    intro i j hij
    have hn : (i, j) ∉ S := fun hm => absurd (hS _ hm) (not_lt.mpr (le_of_lt hij))
    have hij' : j < i := hij
    rw [h i j hn, if_neg (ne_of_gt hij')]
  rw [Matrix.det_of_isUpperTriangular ht]
  refine Finset.prod_eq_one fun i _ => ?_
  have hn : (i, i) ∉ S := fun hm => lt_irrefl _ (hS _ hm)
  rw [h i i hn, if_pos rfl]

def patMat (S : Finset (Fin n × Fin n)) (φ : S → F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if h : (i, j) ∈ S then φ ⟨(i, j), h⟩ else if i = j then 1 else 0

theorem patMat_pat (S : Finset (Fin n × Fin n)) (φ : S → F) : Pat S (patMat S φ) := fun i j h => by
  simp [patMat, h]

def patEquiv (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) :
    {A : GL (Fin n) F // Pat S (A : Matrix (Fin n) (Fin n) F)} ≃ (S → F) where
  toFun A := fun p => (A.1 : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2
  invFun φ := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (patMat S φ)
    (by rw [pat_det S hS _ (patMat_pat S φ)]; exact one_ne_zero), patMat_pat S φ⟩
  left_inv A := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    show patMat S (fun p => (A.1 : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2) i j = (A.1 : Matrix (Fin n) (Fin n) F) i j
    by_cases h : (i, j) ∈ S
    · simp [patMat, h]
    · simp [patMat, h, A.2 i j h]
  right_inv φ := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    show patMat S φ i j = _
    simp [patMat, h]

theorem card_pat [Finite F] (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) :
    Nat.card {A : GL (Fin n) F // Pat S (A : Matrix (Fin n) (Fin n) F)} = Nat.card F ^ S.card := by
  rw [Nat.card_congr (patEquiv S hS), Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]

end Pattern

def upS (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

theorem card_upS (n : ℕ) : (upS n).card = n * (n - 1) / 2 := by
  unfold upS
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have : ∀ j : Fin n, (∑ i : Fin n, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have : (univ.filter fun i : Fin n => i < j) = Finset.Iio j := by ext; simp
    rw [this, Fin.card_Iio]
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

def rowS (k rS n : ℕ) : Finset (Fin n × Fin n) :=
  (upS n).filter fun p => ¬ (p.2.val = rS + k ∧ rS ≤ p.1.val)

theorem card_rowS (k rS n : ℕ) (hn : rS + k < n) : (rowS k rS n).card + k = n * (n - 1) / 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := upS n)
    (fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val)
  rw [card_upS] at h
  have hk : ((upS n).filter fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val).card = k := by
    have : ((upS n).filter fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val) =
        (univ : Finset (Fin k)).image fun i => ((⟨rS + i.val, by omega⟩ : Fin n), (⟨rS + k, hn⟩ : Fin n)) := by
      ext ⟨a, b⟩
      simp only [upS, mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨hab, hb, ha⟩
        have hab' : a.val < b.val := hab
        exact ⟨⟨a.val - rS, by omega⟩, Fin.ext (by simp; omega), Fin.ext (by simp [hb])⟩
      · rintro ⟨i, rfl, rfl⟩
        refine ⟨?_, rfl, by simp⟩
        show rS + i.val < rS + k
        omega
    rw [this, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro i j hij
    have := congrArg (fun p : Fin n × Fin n => p.1.val) hij
    simp at this
    exact Fin.ext this
  unfold rowS
  omega

theorem isUnitri_iff {n : ℕ} {F : Type} [Field F] (A : Matrix (Fin n) (Fin n) F) :
    StandardLattice.IsUnitri A ↔ Pat (upS n) A := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    simp only [upS, mem_filter, mem_univ, true_and, not_lt] at hij
    rcases eq_or_lt_of_le hij with h | h
    · subst h; simp [h2]
    · rw [h1 i j h, if_neg (ne_of_gt h)]
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [h i j (by simp [upS, le_of_lt hij]), if_neg (ne_of_gt hij)]
    · rw [h i i (by simp [upS]), if_pos rfl]

theorem isRowLev_iff {n : ℕ} {F : Type} [Field F] (k rS : ℕ) (A : Matrix (Fin n) (Fin n) F) :
    StandardLattice.IsRowLev k rS A ↔ Pat (rowS k rS n) A := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ i j hij
    by_cases e : i = j
    · subst e; simp [h2]
    rw [if_neg e]
    have e' : i.val ≠ j.val := fun h => e (Fin.ext h)
    simp only [rowS, upS, mem_filter, mem_univ, true_and, not_and] at hij
    by_cases hlt : i < j
    · obtain ⟨hj, hi⟩ : j.val = rS + k ∧ rS ≤ i.val := by
        by_contra hc
        exact hij hlt (fun a b => hc ⟨a, b⟩)
      have hlt' : i.val < j.val := hlt
      exact h4 i j hj e (by unfold StandardLattice.blk; split_ifs <;> omega)
    · have hlt' : j.val < i.val := by
        have : ¬ i.val < j.val := hlt
        omega
      by_cases hb : StandardLattice.blk rS k j.val < StandardLattice.blk rS k i.val
      · exact h1 i j hb
      · refine h3 i j ?_ hlt'
        revert hb
        unfold StandardLattice.blk
        split_ifs <;> omega
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hb hij => ?_, fun i j hj hne hb => ?_⟩
    · have hlt : j.val < i.val := by
        revert hij
        unfold StandardLattice.blk
        split_ifs <;> omega
      have hlt2 : ¬ i < j := fun hh => by
        have : i.val < j.val := hh
        omega
      rw [h i j (by simp [rowS, upS, hlt2]), if_neg (fun e => by subst e; omega)]
    · rw [h i i (by simp [rowS, upS]), if_pos rfl]
    · have hlt2 : ¬ i < j := not_lt.mpr (le_of_lt hij)
      rw [h i j (by simp [rowS, upS, hlt2]), if_neg (ne_of_gt hij)]
    · have hi : rS ≤ i.val := by
        revert hb
        unfold StandardLattice.blk
        split_ifs <;> omega
      rw [h i j (by simp [rowS, hj, hi]), if_neg hne]

end Formalism.MainNotions.J

end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

section Transport

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

def latMap (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V' :=
  M.map ((φ : V →ₗ[K] V').restrictScalars (𝓞 K))

theorem mem_tr (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) (y : V') : y ∈ latMap φ M ↔ φ.symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨φ.symm y, h, by simp⟩

theorem tr_symm_tr (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : latMap φ.symm (latMap φ M) = M := by
  ext x; simp [mem_tr]

theorem tr_tr_symm (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V') : latMap φ (latMap φ.symm M) = M := by
  ext x; simp [mem_tr]

theorem tr_injective (φ : V ≃ₗ[K] V') : Function.Injective (latMap (K := K) φ) := fun a b h => by
  rw [← tr_symm_tr φ a, h, tr_symm_tr]

def cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : V' ≃ₗ[K] V' := (φ.symm.trans g).trans φ

theorem cj_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') : cj φ g y = φ (g (φ.symm y)) := rfl

theorem cj_symm_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') :
    (cj φ g).symm y = φ (g.symm (φ.symm y)) := rfl

theorem cj_symm_cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : cj φ.symm (cj φ g) = g := by
  ext x; simp [cj_apply]

theorem cj_cj_symm (φ : V ≃ₗ[K] V') (g : V' ≃ₗ[K] V') : cj φ (cj φ.symm g) = g := by
  ext x; simp [cj_apply]

theorem mem_gmap (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) (y : V) : y ∈ gmap g M ↔ g.symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨g.symm y, h, by simp⟩

theorem gmap_cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    gmap (cj φ g) (latMap φ M) = latMap φ (gmap g M) := by
  ext y
  simp [mem_gmap, mem_tr, cj_symm_apply]

theorem loc_tr (φ : V ≃ₗ[K] V') (p : Ideal (𝓞 K)) (M : Submodule (𝓞 K) V) :
    loc (K := K) p (latMap φ M) = latMap φ (loc (K := K) p M) := by
  ext y
  rw [mem_tr]
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_tr] at h
    have e : φ.symm (s • y) = s • φ.symm y := by
      rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]
    rwa [e] at h
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_tr]
    have e : φ.symm (s • y) = s • φ.symm y := by
      rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]
    rwa [e]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem isom_symm {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) :
    ∀ x y, h (φ.symm x) (φ.symm y) = h' x y := fun x y => by
  rw [← hφ]; simp

theorem cj_mem_isom {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {g : V ≃ₗ[K] V}
    (hg : g ∈ isom h) : cj φ g ∈ isom h' := by
  intro x y
  rw [cj_apply, cj_apply, hφ, hg, isom_symm hφ]

theorem isLattice_tr (φ : V ≃ₗ[K] V') {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (latMap φ M) where
  fg := hM.fg.map _
  span_eq_top := by
    have h1 : ((latMap φ M : Submodule (𝓞 K) V') : Set V') = (φ : V →ₗ[K] V') '' (M : Set V) := rfl
    rw [h1, Submodule.span_image, hM.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem genus_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L M : Submodule (𝓞 K) V}
    (hM : M ∈ genus h L) : latMap φ M ∈ genus h' (latMap φ L) := by
  refine ⟨isLattice_tr φ hM.1, fun p hp => ?_⟩
  obtain ⟨g, hg, e⟩ := hM.2 p hp
  exact ⟨cj φ g, cj_mem_isom hφ hg, by rw [loc_tr, gmap_cj, e, loc_tr]⟩

theorem classReps_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L : Submodule (𝓞 K) V}
    {s : Finset (Submodule (𝓞 K) V)} (hs : IsClassReps h L s) :
    IsClassReps h' (latMap φ L) (s.map ⟨latMap φ, tr_injective φ⟩) := by
  constructor
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := Finset.mem_map.1 hM
    exact genus_tr hφ (hs.1 N hN)
  · intro M hM
    have hM' : latMap φ.symm M ∈ genus h L := by
      have := genus_tr (isom_symm hφ) hM
      rwa [tr_symm_tr] at this
    obtain ⟨N, ⟨hN, g, hg, e⟩, huniq⟩ := hs.2 _ hM'
    refine ⟨latMap φ N, ⟨Finset.mem_map.2 ⟨N, hN, rfl⟩, cj φ g, cj_mem_isom hφ hg, ?_⟩, ?_⟩
    · rw [gmap_cj, e, tr_tr_symm]
    · rintro N' ⟨hN', g', hg', e'⟩
      obtain ⟨N₀, hN₀, rfl⟩ := Finset.mem_map.1 hN'
      have : N₀ = N := by
        refine huniq N₀ ⟨hN₀, cj φ.symm g', cj_mem_isom (isom_symm hφ) hg', ?_⟩
        have h2 := gmap_cj φ.symm g' (latMap φ N₀)
        rw [tr_symm_tr] at h2
        change gmap g' (latMap φ N₀) = M at e'
        rw [h2, e']
      rw [this]; rfl

theorem card_autL_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) (M : Submodule (𝓞 K) V) :
    Nat.card (autL h' (latMap φ M)) = Nat.card (autL h M) := by
  have a1 : ∀ g : autL h M, gmap (cj φ g.1) (latMap φ M) = latMap φ M := fun g => by
    rw [gmap_cj, g.2.2]
  have a2 : ∀ g : autL h' (latMap φ M), gmap (cj φ.symm g.1) M = M := fun g => by
    have h2 := gmap_cj φ.symm g.1 (latMap φ M)
    rw [tr_symm_tr] at h2
    rw [h2, g.2.2, tr_symm_tr]
  exact (Nat.card_congr ⟨fun g => ⟨cj φ g.1, cj_mem_isom hφ g.2.1, a1 g⟩,
    fun g => ⟨cj φ.symm g.1, cj_mem_isom (isom_symm hφ) g.2.1, a2 g⟩,
    fun g => Subtype.ext (cj_symm_cj φ g.1), fun g => Subtype.ext (cj_cj_symm φ g.1)⟩).symm

theorem mass_eq_sum (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (s : Finset (Submodule (𝓞 K) V)) (hs : IsClassReps h L s) :
    mass h L = ∑ M ∈ s, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ := by
  rw [massBasic_mass_eq h L ⟨s, hs⟩]
  apply Complex.ofReal_injective
  rw [massBasic_sum_cast, massBasic_sum_cast]
  exact latLiftIndep K V h L _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _
    (Exists.choose_spec (⟨s, hs⟩ : ∃ s, IsClassReps h L s)) hs

theorem mass_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) (L : Submodule (𝓞 K) V) :
    mass h' (latMap φ L) = mass h L := by
  by_cases hs : ∃ s, IsClassReps h L s
  · obtain ⟨s, hs⟩ := hs
    rw [mass_eq_sum h L s hs, mass_eq_sum h' _ _ (classReps_tr hφ hs), Finset.sum_map]
    exact Finset.sum_congr rfl fun M _ => by
      rw [Function.Embedding.coeFn_mk, card_autL_tr hφ]
  · have hs' : ¬ ∃ s, IsClassReps h' (latMap φ L) s := by
      rintro ⟨s, hs'⟩
      apply hs
      have := classReps_tr (isom_symm hφ) hs'
      rw [tr_symm_tr] at this
      exact ⟨_, this⟩
    unfold mass
    rw [dif_neg hs, dif_neg hs']

theorem mass_ortho_eq {n : ℕ} {L : Submodule (𝓞 K) V} {L' : Submodule (𝓞 K) V'}
    (hL : IsOrthoLattice h L n) (hL' : IsOrthoLattice h' L' n) : mass h L = mass h' L' := by
  obtain ⟨e, he1, he2, rfl, he⟩ := hL
  obtain ⟨e', he1', he2', rfl, he'⟩ := hL'
  let b : Module.Basis (Fin n) K V := Module.Basis.mk he1 he2.ge
  let b' : Module.Basis (Fin n) K V' := Module.Basis.mk he1' he2'.ge
  let φ : V ≃ₗ[K] V' := b.equiv b' (Equiv.refl _)
  have hφe : ∀ i, φ (e i) = e' i := fun i => by
    have := b.equiv_apply i b' (Equiv.refl _)
    simpa [b, b', φ] using this
  have hφ : ∀ x y, h' (φ x) (φ y) = h x y := by
    intro x y
    have hx := b.sum_repr x
    have hy := b.sum_repr y
    rw [← hx, ← hy]
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, b,
      Module.Basis.mk_apply, hφe, he, he']
  rw [← mass_tr hφ]
  congr 1
  unfold latMap
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext i
  exact hφe i

end Transport

end Formalism.MainNotions.J

end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stdForm_apply (K : Type) [Field K] [StarRing K] (M : ℕ) (x y : Fin M → K) :
    StandardLattice.stdForm K M x y = ∑ i, star (x i) * y i := rfl

theorem std_ortho (K : Type) [Field K] [NumberField K] [StarRing K] (M : ℕ) :
    IsOrthoLattice (StandardLattice.stdForm K M) (StandardLattice.stdLat K M) M := by
  have e : (fun i : Fin M => (Pi.single i 1 : Fin M → K)) = Pi.basisFun K (Fin M) := by
    funext i; simp
  refine ⟨fun i => Pi.single i 1, ?_, ?_, rfl, fun i j => ?_⟩
  · rw [e]; exact (Pi.basisFun K (Fin M)).linearIndependent
  · rw [e]; exact (Pi.basisFun K (Fin M)).span_eq
  · by_cases hij : i = j
    · subst hij; simp [stdForm_apply, Pi.single_apply]
    · simp [stdForm_apply, Pi.single_apply, hij, Ne.symm hij]



theorem zetaR_eq (M : ℕ) (hM : 2 ≤ M) : (riemannZeta (M : ℂ)).re = StandardLattice.zetaR M := by
  have h1 : (1 : ℝ) < ((M : ℂ)).re := by
    simp only [Complex.natCast_re]; exact_mod_cast hM
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1]
  have h2 : (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (M : ℂ)) = ((StandardLattice.zetaR M : ℝ) : ℂ) := by
    unfold StandardLattice.zetaR
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [Complex.cpow_natCast]
    push_cast
    rfl
  rw [h2, Complex.ofReal_re]


end Formalism.MainNotions.J

end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IdxColTie (D : D7) : Prop := StandardLattice.idxPi D (D.host.g 0) (D.host.g 1) = S.gaG D

def IdxRowTie (D : D7) : Prop := StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) = LocalBesselAndTopKernel.idxRows D

def ColHyp (D : D7) : Prop :=
  StandardLattice.GBig D ∧ (∀ i, StandardLattice.SplitsF D (D.host.g i)) ∧ ∀ u : D.what₂.Word, StandardLattice.SplitsF D (D.mem u).A.T ∧ StandardLattice.Mu0Tie D u





end Formalism.MainNotions.J

end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open Finset NumberField IsDedekindDomain Formalism.BasicNotions

theorem card_GL_real (g n : ℕ) [Fact g.Prime] :
    (Nat.card (GL (Fin n) (ZMod g)) : ℝ) = LocalBesselAndTopKernel.cardGL (g : ℝ) n := by
  rw [Matrix.card_GL_field, ZMod.card]
  unfold LocalBesselAndTopKernel.cardGL
  rw [Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => ((g ^ n - g ^ i : ℕ) : ℝ)) n]
  refine prod_congr rfl fun i hi => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right (Fact.out : g.Prime).pos (le_of_lt (mem_range.mp hi)))]
  push_cast
  rfl

theorem cardGL_factor (q : ℝ) (k : ℕ) :
    LocalBesselAndTopKernel.cardGL q k = q ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 1 k, (q ^ i - 1) := by
  unfold LocalBesselAndTopKernel.cardGL
  have h1 : ∀ i ∈ range k, q ^ k - q ^ i = q ^ i * (q ^ (k - 1 - i + 1) - 1) := by
    intro i hi
    have hi' := mem_range.mp hi
    have : k = i + (k - 1 - i + 1) := by omega
    conv_lhs => rw [this, pow_add]
    ring
  rw [prod_congr rfl h1, prod_mul_distrib, prod_pow_eq_pow_sum, sum_range_id,
    prod_range_reflect (fun j => q ^ (j + 1) - 1) k]
  congr 1
  rw [range_eq_Ico, prod_Ico_add' (fun j => q ^ j - 1) 0 k 1]
  refine prod_congr ?_ fun _ _ => rfl
  ext x
  simp only [mem_Ico, mem_Icc]
  omega

theorem idxColLoc_eq (g k : ℕ) [Fact g.Prime] :
    StandardLattice.idxColLoc g k = ∏ i ∈ Finset.Icc 1 k, ((g : ℝ) ^ i - 1) := by
  unfold StandardLattice.idxColLoc StandardLattice.idxLoc
  have hc : Nat.card {A : GL (Fin k) (ZMod g) // StandardLattice.IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} =
      g ^ (k * (k - 1) / 2) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun A : GL (Fin k) (ZMod g) =>
      isUnitri_iff (A : Matrix (Fin k) (Fin k) (ZMod g))), card_pat _ (by simp [upS]), card_upS, Nat.card_zmod]
  have hg : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  rw [card_GL_real, hc, cardGL_factor, Nat.cast_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hg)]

theorem dim_arith (k r c : ℕ) (h : c + k = (k + 2 * r + 1) * (k + 2 * r + 1 - 1) / 2) :
    c = r * (2 * k + 2 * r + 1) + k * (k - 1) / 2 := by
  rcases k with _ | k
  · have e : (0 + 2 * r + 1) * (0 + 2 * r + 1 - 1) = 2 * (r * (2 * 0 + 2 * r + 1)) + 0 := by
      simp only [Nat.add_sub_cancel]; ring
    rw [e, Nat.mul_add_div (by norm_num)] at h
    omega
  · have e : (k + 1 + 2 * r + 1) * (k + 1 + 2 * r + 1 - 1) =
        2 * (r * (2 * (k + 1) + 2 * r + 1) + (k + 1)) + (k + 1) * (k + 1 - 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [e, Nat.mul_add_div (by norm_num)] at h
    omega

theorem idxRowLoc_eq (g k m : ℕ) [Fact g.Prime] (hm : Even m) (h2 : 2 ≤ m) :
    StandardLattice.idxRowLoc g k m = LocalBesselAndTopKernel.cardGL (g : ℝ) (k + m - 1) /
      ((g : ℝ) ^ ((m / 2 - 1) * (2 * k + 2 * (m / 2 - 1) + 1)) * (g : ℝ) ^ (k * (k - 1) / 2)) := by
  unfold StandardLattice.idxRowLoc StandardLattice.idxLoc
  obtain ⟨a, rfl⟩ := hm
  have ha : (a + a) / 2 - 1 = a - 1 := by omega
  have hn : k + (a + a) - 1 = k + 2 * (a - 1) + 1 := by omega
  have hc : Nat.card {A : GL (Fin (k + (a + a) - 1)) (ZMod g) //
      StandardLattice.IsRowLev k ((a + a) / 2 - 1) (A : Matrix (Fin (k + (a + a) - 1)) (Fin (k + (a + a) - 1)) (ZMod g))} =
      g ^ (((a + a) / 2 - 1) * (2 * k + 2 * ((a + a) / 2 - 1) + 1) + k * (k - 1) / 2) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun A : GL (Fin (k + (a + a) - 1)) (ZMod g) =>
      isRowLev_iff k ((a + a) / 2 - 1) (A : Matrix (Fin (k + (a + a) - 1)) (Fin (k + (a + a) - 1)) (ZMod g))),
      card_pat _ (by simp only [rowS, upS, mem_filter, mem_univ, true_and]; exact fun p hp => hp.1), Nat.card_zmod]
    congr 1
    have h := card_rowS k ((a + a) / 2 - 1) (k + (a + a) - 1) (by omega)
    rw [ha] at h ⊢
    rw [hn] at h ⊢
    exact dim_arith k (a - 1) _ h
  rw [card_GL_real, hc, Nat.cast_pow, pow_add]

theorem finprod_typed (D : D7) (h : ∀ i, StandardLattice.SplitsF D (D.host.g i)) (φ : ℕ → ℝ) :
    ∏ᶠ p ∈ S.typedPl D, φ (Ideal.absNorm p.asIdeal) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  have hf : D.R.f ≠ 0 := by
    unfold Ranks.f Ranks.n
    positivity
  have hfin : ∀ i, ({p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}).Finite := by
    intro i
    have hc := (h i).1
    have hF : Finite {p : HeightOneSpectrum (𝓞 D.host.F) // ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact hf)
    exact Set.finite_coe_iff.mp hF
  have hone : ∀ i, ∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal) = φ (D.host.g i) ^ D.R.f := by
    intro i
    have e : ∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal},
        φ (Ideal.absNorm p.asIdeal) =
        ∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal},
          φ (D.host.g i) :=
      finprod_mem_congr rfl fun p hp => by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, (h i).2 p hp]
    rw [e, finprod_mem_eq_finite_toFinset_prod _ (hfin i), Finset.prod_const,
      ← Set.ncard_eq_toFinset_card _ (hfin i), ← Nat.card_coe_set_eq]
    exact congrArg _ (h i).1
  have hdis : Disjoint {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}
      {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} := by
    refine Set.disjoint_left.mpr fun p h0 h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
      (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).mpr D.host.g_ne
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hab' : (a : 𝓞 D.host.F) * ((D.host.g 0 : ℕ) : 𝓞 D.host.F) + (b : 𝓞 D.host.F) * ((D.host.g 1 : ℕ) : 𝓞 D.host.F) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.F) hab
    rw [← hab']
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)
  have hU : S.typedPl D = {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} ∪
      {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal} := rfl
  rw [hU, finprod_mem_union hdis (hfin 0) (hfin 1), hone 0, hone 1]

theorem idxColTie_of (D : D7) (h : ∀ i, StandardLattice.SplitsF D (D.host.g i)) : IdxColTie D := by
  have : ∀ i, Fact (D.host.g i).Prime := fun i => ⟨D.host.g_prime i⟩
  unfold IdxColTie StandardLattice.idxPi S.gaG
  rw [finprod_typed D h (fun N => ∏ i ∈ Finset.Icc 1 D.R.k, ((N : ℝ) ^ i - 1)), idxColLoc_eq, idxColLoc_eq]

theorem idxRowTie_of (D : D7) (h : ∀ i, StandardLattice.SplitsF D (D.host.g i)) : IdxRowTie D := by
  have : ∀ i, Fact (D.host.g i).Prime := fun i => ⟨D.host.g_prime i⟩
  unfold IdxRowTie StandardLattice.idxSig LocalBesselAndTopKernel.idxRows
  rw [finprod_typed D h (fun N => LocalBesselAndTopKernel.cardGL (N : ℝ) D.R.r /
    ((N : ℝ) ^ LocalBesselAndTopKernel.dimNS D * (N : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))),
    idxRowLoc_eq _ _ _ D.R.m_even D.R.two_le_m, idxRowLoc_eq _ _ _ D.R.m_even D.R.two_le_m]
  rfl



end Formalism.MainNotions.J

end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open Ideal NumberField IsDedekindDomain

section Split

variable (K : Type) [Field K] [NumberField K] (p : ℕ)

theorem pI_ne_bot (hp : p.Prime) : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

theorem pI_max (hp : p.Prime) : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible

theorem liesOver_ne_bot (hp : p.Prime) (I : Ideal (𝓞 K)) (hI : I.LiesOver (span {(p : ℤ)})) : I ≠ ⊥ := by
  intro h
  have h1 : (span {(p : ℤ)} : Ideal ℤ) = I.under ℤ := hI.over
  rw [h, Ideal.under, Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int] at h1
  exact pI_ne_bot p hp h1

theorem img_places (hp : p.Prime) :
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal} =
      (span {(p : ℤ)}).primesOver (𝓞 K) := by
  haveI := pI_max p hp
  ext P
  simp only [Set.mem_image, Set.mem_setOf_eq, Ideal.primesOver]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨?_⟩⟩
    have hle : (span {(p : ℤ)} : Ideal ℤ) ≤ v.asIdeal.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 K) (p : ℤ) ∈ v.asIdeal
      simpa using hv
    exact (pI_max p hp).eq_of_le (v.isPrime.comap (algebraMap ℤ (𝓞 K))).ne_top hle
  · rintro ⟨hPp, hPl⟩
    refine ⟨⟨P, hPp, liesOver_ne_bot K p hp P hPl⟩, ?_, rfl⟩
    have h1 : (p : ℤ) ∈ P.under ℤ := by
      rw [← hPl.over]
      exact Ideal.mem_span_singleton_self _
    simpa using h1

theorem ncard_places (hp : p.Prime) :
    ({v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}).ncard =
      (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card := by
  haveI := pI_max p hp
  rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset (pI_ne_bot p hp), ← img_places K p hp,
    Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h)]

theorem map_pI_ne_bot (hp : p.Prime) : map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≠ ⊥ := by
  rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot, map_natCast]
  exact_mod_cast hp.ne_zero

theorem ef_pos (hp : p.Prime) (P : Ideal (𝓞 K)) (hP : P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)) :
    1 ≤ (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P := by
  haveI := pI_max p hp
  obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff (pI_ne_bot p hp) (𝓞 K)).mp hP
  have he : 0 < (span {(p : ℤ)}).ramificationIdx' P := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (pI_ne_bot p hp)]
    exact Ideal.ramificationIdx_pos P ℤ
  have hf : 0 < (span {(p : ℤ)}).inertiaDeg' P := Ideal.inertiaDeg'_pos _ _
  exact Nat.mul_pos he hf

theorem sum_ef (hp : p.Prime) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = Module.finrank ℚ K := by
  haveI := pI_max p hp
  exact Ideal.sum_ramification_inertia (𝓞 K) ℚ K (pI_ne_bot p hp)

theorem ef_one_of_card (hp : p.Prime)
    (h : (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card = Module.finrank ℚ K) :
    ∀ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = 1 := by
  intro P hP
  have h1 : ∑ _Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K), 1 =
      ∑ Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
        (span {(p : ℤ)}).ramificationIdx' Q * (span {(p : ℤ)}).inertiaDeg' Q := by
    rw [sum_ef K p hp, ← h, Finset.sum_const, smul_eq_mul, mul_one]
  exact ((Finset.sum_eq_sum_iff_of_le (fun Q hQ => ef_pos K p hp Q hQ)).mp h1 P hP).symm

theorem card_of_ef_one (hp : p.Prime)
    (h : ∀ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = 1) :
    (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card = Module.finrank ℚ K := by
  rw [← sum_ef K p hp, Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_one]

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

theorem ef_one_sub (hp : p.Prime)
    (hL : ∀ Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 L),
      (span {(p : ℤ)}).ramificationIdx' Q * (span {(p : ℤ)}).inertiaDeg' Q = 1) :
    ∀ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = 1 := by
  intro P hP
  haveI := pI_max p hp
  obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff (pI_ne_bot p hp) (𝓞 K)).mp hP
  have hPne : P ≠ ⊥ := liesOver_ne_bot K p hp P hPl
  haveI : P.IsMaximal := hPp.isMaximal hPne

  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) P
  haveI := hQl
  haveI hQp : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  have hQ : Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff (pI_ne_bot p hp) (𝓞 L)).mpr ⟨hQm.isPrime, hQp⟩
  have h1 := hL Q hQ
  have hmapP : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) P ≠ ⊥ := by
    intro h
    apply hPne
    have h2 : P ≤ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) P).comap (algebraMap (𝓞 K) (𝓞 L)) := Ideal.le_comap_map
    rw [h, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))] at h2
    exact le_bot_iff.mp h2
  have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) P ≤ Q := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq hQl.over
  have he := Ideal.ramificationIdx'_algebra_tower (p := span {(p : ℤ)}) (P := P) (Q := Q) hmapP
    (map_pI_ne_bot L p hp) hle
  have hf := Ideal.inertiaDeg'_algebra_tower (span {(p : ℤ)}) P Q
  rw [he, hf] at h1
  have h3 : ((span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P) *
      (P.ramificationIdx' Q * P.inertiaDeg' Q) = 1 := by
    rw [← h1]
    ring
  exact Nat.eq_one_of_mul_eq_one_right h3

theorem splits_sub (hp : p.Prime)
    (h : ({w : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ w.asIdeal}).ncard = Module.finrank ℚ L) :
    Nat.card {v : HeightOneSpectrum (𝓞 K) // ((p : ℕ) : 𝓞 K) ∈ v.asIdeal} = Module.finrank ℚ K ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal → Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
  haveI := pI_max p hp
  have hL : (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 L)).card = Module.finrank ℚ L := by
    rw [← ncard_places L p hp]
    exact h
  have hefK := ef_one_sub K p L hp (ef_one_of_card L p hp hL)
  refine ⟨?_, ?_⟩
  · rw [← card_of_ef_one K p hp hefK, ← ncard_places K p hp]
    exact Nat.card_coe_set_eq _
  · intro v hv
    have hmem : v.asIdeal ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K) := by
      rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset (pI_ne_bot p hp), ← img_places K p hp]
      exact ⟨v, hv, rfl⟩
    obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff (pI_ne_bot p hp) (𝓞 K)).mp hmem
    have hf1 : (span {(p : ℤ)}).inertiaDeg' v.asIdeal = 1 := Nat.eq_one_of_mul_eq_one_left (hefK _ hmem)
    have hn := Ideal.absNorm_eq_pow_inertiaDeg' (R := 𝓞 K) (p := p) v.asIdeal hp
    rw [hf1, pow_one] at hn
    rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end Split

end Formalism.MainNotions.J

end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.BasicNotions

theorem finrank_F_eq (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  exact D.host.der.finrank_F

theorem splitsF_g (D : D7) (i : Fin 2) : StandardLattice.SplitsF D (D.host.g i) := by
  have h := splits_sub D.host.F (D.host.g i) D.host.E (D.host.g_prime i) (D.nd.g_split i)
  rw [finrank_F_eq] at h
  exact h

theorem idxColTie_holds (D : D7) : IdxColTie D := idxColTie_of D (splitsF_g D)

theorem idxRowTie_holds (D : D7) : IdxRowTie D := idxRowTie_of D (splitsF_g D)

def ColHyp0 (D : D7) : Prop :=
  StandardLattice.GBig D ∧ ∀ u : D.what₂.Word, StandardLattice.SplitsF D (D.mem u).A.T ∧ StandardLattice.Mu0Tie D u





end Formalism.MainNotions.J

end
end
