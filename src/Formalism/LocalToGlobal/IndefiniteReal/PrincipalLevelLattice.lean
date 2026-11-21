import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx.PrincipalLevelLattice

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

def principalHermitianLattice : Formalism.BasicNotions.HLat K := toHLat (X.XE cr b) (X.data cr b).RR




def jEEx (σ : K →+* ℂ) : (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) →ₛₗ[σ] X.EE :=
  (X.iC cr b Bs.μ0).comp (cptL σ _)

theorem jEEx_apply (σ : K →+* ℂ) (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    jEEx X cr b σ x = X.iC cr b Bs.μ0 (cpt σ x) := rfl

theorem cpt_single (σ : K →+* ℂ) {n : ℕ} (i : Fin n) : cpt σ (Pi.single i (1 : K)) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [cpt]
  · simp [cpt, Pi.single_apply, h]



structure RowsId (c : ℂ →+* ℂ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  c_cases : c = RingHom.id ℂ ∨ c = starRingEnd ℂ
  e : E →ₛₗ[c] X.EE
  range_e : Set.range e = (X.EEl b : Set X.EE)
  inner_e : ∀ x y : E, ⟪e x, e y⟫_ℂ = ((X.nP b : ℝ) : ℂ) * c ⟪x, y⟫_ℂ

variable {X b} {c : ℂ →+* ℂ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem RowsId.c_c (I : RowsId X b c E) (z : ℂ) : c (c z) = z := by
  rcases I.c_cases with rfl | rfl <;> simp

theorem RowsId.c_real (I : RowsId X b c E) {z : ℂ} (hz : starRingEnd ℂ z = z) : c z = z := by
  rcases I.c_cases with rfl | rfl
  · rfl
  · exact hz

theorem RowsId.e_injective (I : RowsId X b c E) (hn : 0 < X.nP b) : Function.Injective I.e := by
  intro x y hxy
  have h0 : I.e (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h1 := I.inner_e (x - y) (x - y)
  rw [h0, inner_zero_left] at h1
  have hne : ((X.nP b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : c ⟪x - y, x - y⟫_ℂ = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd h hne
    · exact h
  have h3 : ⟪x - y, x - y⟫_ℂ = 0 := by rw [← I.c_c ⟪x - y, x - y⟫_ℂ, h2, map_zero]
  rw [inner_self_eq_zero, sub_eq_zero] at h3
  exact h3

variable (X b)

theorem iC_mem_range (h2 : X.H2 cr b) (I : RowsId X b c E) (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ) :
    ∃ w, I.e w = X.iC cr b Bs.μ0 y := by
  have hy : X.iC cr b Bs.μ0 y ∈ (X.EEl b : Set X.EE) := by
    rw [← h2.2.2]
    exact LinearMap.mem_range_self _ y
  rw [← I.range_e] at hy
  obtain ⟨w, hw⟩ := hy
  exact ⟨w, hw⟩

def rowsMap (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) : (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ) →ₛₗ[c] E where
  toFun y := Classical.choose (iC_mem_range X cr b h2 I y)
  map_add' y z := I.e_injective hn (by
    have h1 := Classical.choose_spec (iC_mem_range X cr b h2 I (y + z))
    have h3 := Classical.choose_spec (iC_mem_range X cr b h2 I y)
    have h4 := Classical.choose_spec (iC_mem_range X cr b h2 I z)
    rw [h1, map_add I.e, h3, h4, map_add])
  map_smul' a y := I.e_injective hn (by
    have h1 := Classical.choose_spec (iC_mem_range X cr b h2 I (a • y))
    have h3 := Classical.choose_spec (iC_mem_range X cr b h2 I y)
    rw [h1, map_smulₛₗ I.e, h3, I.c_c, map_smul])

theorem e_rowsMap (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ) :
    I.e (rowsMap X cr b h2 I hn y) = X.iC cr b Bs.μ0 y :=
  Classical.choose_spec (iC_mem_range X cr b h2 I y)

theorem rowsMap_bijective (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) :
    Function.Bijective (rowsMap X cr b h2 I hn) := by
  constructor
  · intro y z hyz
    apply h2.1
    rw [← e_rowsMap X cr b h2 I hn y, ← e_rowsMap X cr b h2 I hn z, hyz]
  · intro w
    have hw : I.e w ∈ (X.EEl b : Set X.EE) := by
      rw [← I.range_e]
      exact ⟨w, rfl⟩
    rw [← h2.2.2, SetLike.mem_coe, LinearMap.mem_range] at hw
    obtain ⟨y, hy⟩ := hw
    exact ⟨y, I.e_injective hn (by rw [e_rowsMap, hy])⟩

def jEE (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a)) :
    (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) →ₛₗ[σ] E where
  toFun x := rowsMap X cr b h2 I hn (cptL Bs.v0.embedding _ x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' a x := by
    show rowsMap X cr b h2 I hn (cptL Bs.v0.embedding _ (a • x)) = σ a • rowsMap X cr b h2 I hn (cptL Bs.v0.embedding _ x)
    rw [map_smulₛₗ, map_smulₛₗ, hc a, I.c_c]

theorem jEE_apply (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a))
    (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) : jEE X cr b h2 I hn σ hc x = rowsMap X cr b h2 I hn (cpt Bs.v0.embedding x) := rfl

theorem e_jEE (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a))
    (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) : I.e (jEE X cr b h2 I hn σ hc x) = jEEx X cr b Bs.v0.embedding x := by
  rw [jEE_apply, e_rowsMap, jEEx_apply]


theorem jEE_basis (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a)) :
    LinearIndependent ℂ (fun i => jEE X cr b h2 I hn σ hc (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) i)) ∧
      Submodule.span ℂ (Set.range (fun i => jEE X cr b h2 I hn σ hc (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) i))) = ⊤ := by
  have hf : (fun i => jEE X cr b h2 I hn σ hc (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) i)) =
      fun i => rowsMap X cr b h2 I hn (Pi.single i 1) := by
    funext i
    rw [Pi.basisFun_apply, jEE_apply, cpt_single]
  have hsm : ∀ (z : ℂ) (w : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ), z • rowsMap X cr b h2 I hn w = rowsMap X cr b h2 I hn (c z • w) := by
    intro z w; rw [map_smulₛₗ, I.c_c]
  rw [hf]
  refine ⟨?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    simp_rw [hsm, ← map_sum] at hg
    have h0 : ∑ j, c (g j) • (Pi.single j 1 : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ) = 0 :=
      (rowsMap_bijective X cr b h2 I hn).1 (hg.trans (map_zero _).symm)
    have h1 := congrFun h0 i
    simpa [Finset.sum_apply, Pi.single_apply] using h1
  · rw [eq_top_iff]
    intro w _
    obtain ⟨y, rfl⟩ := (rowsMap_bijective X cr b h2 I hn).2 w
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨fun i => c (y i), ?_⟩
    simp_rw [hsm, I.c_c, ← map_sum]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]

theorem frame_at_base_place_eq_gram : (X.XE cr b) Bs.v0 = frameOf (X.gramE cr b) := by
  show rowXE _ _ _ _ Bs.v0 = _
  simp [rowXE, rowFrame, spliceFrame]

theorem frames (hW : (lv (fc X.zs) b).WF) (h2 : X.H2 cr b) (hp : X.H4pos) :
    ∀ v, IsUnit ((principalHermitianLattice X cr b).X v).det :=
  (rowXE_spec (Df := lv (fc X.zs) b) hW _ (X.gramE_unit cr b h2 (hp.2.2 b)) X.κ hp.1
    (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hp.2.1 j Bs.μ0 p v)).1

theorem majorant_at_base_place_eq_inner (h2 : X.H2 cr b) (hn : 0 < X.nP b) (x y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (X.XE cr b) Bs.v0 x y =
      (((X.nP b)⁻¹ : ℝ) : ℂ) * ⟪jEEx X cr b Bs.v0.embedding x, jEEx X cr b Bs.v0.embedding y⟫_ℂ := by
  have hli : LinearIndependent ℂ (fun i => X.iC cr b Bs.μ0 (Pi.single i 1)) :=
    li_of_lin_injective (by rw [lin_basis]; exact h2.1)
  rw [majAt_gram_smul (X.XE cr b) Bs.v0 _ hli _ (inv_pos.mpr hn) (frame_at_base_place_eq_gram X cr b), lin_basis]
  rfl

theorem jEE_inner (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a))
    (x y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (X.XE cr b) Bs.v0 x y = c ⟪jEE X cr b h2 I hn σ hc x, jEE X cr b h2 I hn σ hc y⟫_ℂ := by
  rw [majorant_at_base_place_eq_inner X cr b h2 hn, ← e_jEE X cr b h2 I hn σ hc, ← e_jEE X cr b h2 I hn σ hc, I.inner_e, ← mul_assoc,
    ← Complex.ofReal_mul, inv_mul_cancel₀ hn.ne', Complex.ofReal_one, one_mul]

theorem jEE_norm (h2 : X.H2 cr b) (I : RowsId X b c E) (hn : 0 < X.nP b) (σ : K →+* ℂ) (hc : ∀ a, Bs.v0.embedding a = c (σ a))
    (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K _) (X.XE cr b) Bs.v0 x = ‖jEE X cr b h2 I hn σ hc x‖ := by
  have h : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (X.XE cr b) Bs.v0 x x =
      ⟪jEE X cr b h2 I hn σ hc x, jEE X cr b h2 I hn σ hc x⟫_ℂ := by
    rw [jEE_inner X cr b h2 I hn σ hc x x, I.c_real (inner_conj_symm _ _)]
  rw [← Real.sqrt_sq (norm_nonneg (jEE X cr b h2 I hn σ hc x)), ← inner_self_eq_norm_sq (𝕜 := ℂ), ← h]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  congr 1
  have hz : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  simp_rw [hz]
  rw [← Complex.ofReal_sum]
  exact (Complex.ofReal_re _).symm






theorem RR_lattice (hW : (lv (fc X.zs) b).WF) (h0 : X.H0) (h2 : X.H2 cr b) (hr : X.RATmu cr b) :
    Submodule.IsLattice K (principalHermitianLattice X cr b).L ∧ ∀ w : HeightOneSpectrum (𝓞 K),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (principalHermitianLattice X cr b).L =
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (X.rowMat cr b (X.μ w)) ((lv (fc X.zs) b).abelian₂ (X.μ w))) :=
  RR_spec hW (X.data cr b) h0 (fun t => (X.rowMat_bij cr b h2 hr t).2)



theorem RR_mem (hW : (lv (fc X.zs) b).WF) (h0 : X.H0) (h2 : X.H2 cr b) (hr : X.RATmu cr b)
    (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    x ∈ (principalHermitianLattice X cr b).L ↔ ∀ w : HeightOneSpectrum (𝓞 K), ∃ d : 𝓞 K, d ∉ w.asIdeal ∧
      d • x ∈ matLat (X.rowMat cr b (X.μ w)) ((lv (fc X.zs) b).abelian₂ (X.μ w)) := by
  have hloc := (RR_lattice X cr b hW h0 h2 hr).2
  have key : ∀ (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K))
      (y : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K),
      y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • y ∈ L := fun _ _ _ => Iff.rfl
  constructor
  · intro hx w
    have h1 : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (principalHermitianLattice X cr b).L :=
      (key w _ x).2 ⟨1, w.asIdeal.primeCompl.one_mem, (principalHermitianLattice X cr b).L.smul_mem 1 hx⟩
    rw [hloc w] at h1
    obtain ⟨d, hd, hdx⟩ := (key w _ x).1 h1
    exact ⟨d, hd, hdx⟩
  · intro hx
    by_contra hxL
    let I : Ideal (𝓞 K) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) _ x) (principalHermitianLattice X cr b).L
    have hmem : ∀ r : 𝓞 K, r ∈ I ↔ r • x ∈ (principalHermitianLattice X cr b).L := fun r => Iff.rfl
    have hI : I ≠ ⊤ := by
      intro h
      apply hxL
      have h1 : (1 : 𝓞 K) ∈ I := h ▸ Submodule.mem_top
      simpa using (hmem 1).mp h1
    obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
    have hpb : p ≠ ⊥ := by
      intro hb
      subst hb
      exact NumberField.RingOfIntegers.not_isField K (Ring.isField_iff_maximal_bot.2 hp)
    let w : HeightOneSpectrum (𝓞 K) := ⟨p, hp.isPrime, hpb⟩
    obtain ⟨d, hd, hdx⟩ := hx w
    have h1 : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (X.rowMat cr b (X.μ w)) ((lv (fc X.zs) b).abelian₂ (X.μ w))) :=
      (key w _ x).2 ⟨d, hd, hdx⟩
    rw [← hloc w] at h1
    obtain ⟨s, hs, hsx⟩ := (key w _ x).1 h1
    exact hs (hIp ((hmem s).2 hsx))


end Formalism.IndefR.Cx.PrincipalLevelLattice

end
