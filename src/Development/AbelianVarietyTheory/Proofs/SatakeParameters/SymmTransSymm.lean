import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicLatticeCompletionLocalGlobal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MulVecMemLocLatIffOfFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesCongruentOneOfSameBadPlaceComponents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFrames
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTwistPrimeInvariantCongruentFrames

section
namespace GlobalTheory.FiniteIndexSubgroup

open NumberField

private theorem exists_ne_zero_smul_mem_of_mem_span' {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) :
    ∀ x ∈ Submodule.span E (L : Set (Fin n → E)), ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • z = a • (b • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact L.add_mem (L.smul_mem b hax) (L.smul_mem a hbz)
  | smul c x _ hx =>
    obtain ⟨ν, hν, hνx⟩ := hx
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb' : algebraMap (RingOfIntegers E) E b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hsc : algebraMap (RingOfIntegers E) E (b * ν) * c = algebraMap (RingOfIntegers E) E (a * ν) := by
      rw [← hab, map_mul, map_mul]
      field_simp
    refine ⟨b * ν, mul_ne_zero hb0 hν, ?_⟩
    have : (b * ν) • (c • x) = a • (ν • x) := by
      calc (b * ν) • (c • x) = (algebraMap (RingOfIntegers E) E (b * ν)) • (c • x) :=
            (algebraMap_smul E _ _).symm
        _ = (algebraMap (RingOfIntegers E) E (b * ν) * c) • x := smul_smul _ _ _
        _ = (algebraMap (RingOfIntegers E) E (a * ν)) • x := by rw [hsc]
        _ = (a * ν) • x := algebraMap_smul E _ _
        _ = a • (ν • x) := mul_smul _ _ _
    rw [this]
    exact L.smul_mem a hνx

theorem main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • y ∈ L := exists_ne_zero_smul_mem_of_mem_span' L y (by rw [hL]; exact Submodule.mem_top)

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∀ (y : Fin n → E), ∃ (ν : NumberField.RingOfIntegers E), ν ≠ (0 : NumberField.RingOfIntegers E) ∧ ν • y ∈ L := by
  intro E _ _ n L hL y
  exact exists_ne_zero_smul_mem_of_mem_span' L y (by rw [hL]; exact Submodule.mem_top)

end GlobalTheory.FiniteIndexSubgroup
end

section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV.AwayLat

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem localization_mono {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (p : Ideal (𝓞 E)) [p.IsPrime]
    {L N : Submodule (𝓞 E) W} (h : L ≤ N) : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p N := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem localization_le_of_le_localization₂ {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (p : Ideal (𝓞 E)) [p.IsPrime]
    {L N : Submodule (𝓞 E) W} (h : L ≤ Formalism.HermitianLatticesTheory.localization₂ p N) : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p N := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hx'⟩ := h hx
  exact ⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact hx'⟩

theorem sup_smul_le_locP {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (p : Ideal (𝓞 E)) [p.IsPrime]
    (I : Ideal (𝓞 E)) {A A' B B' : Submodule (𝓞 E) W} (hA : A ≤ Formalism.HermitianLatticesTheory.localization₂ p A') (hB : B ≤ Formalism.HermitianLatticesTheory.localization₂ p B') :
    A ⊔ I • B ≤ Formalism.HermitianLatticesTheory.localization₂ p (A' ⊔ I • B') := by
  refine sup_le (hA.trans (localization_mono p le_sup_left)) ?_
  refine Submodule.smul_le.2 fun r hr m hm => ?_
  obtain ⟨s, hs, hsm⟩ := hB hm
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hsm)

theorem map_le_locP {n : ℕ} (p : Ideal (𝓞 E)) [p.IsPrime] (f : (Fin n → E) ≃ₗ[E] (Fin n → E))
    {M M' : Submodule (𝓞 E) (Fin n → E)} (h : M ≤ Formalism.HermitianLatticesTheory.localization₂ p M') :
    M.map ((f : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ≤
      Formalism.HermitianLatticesTheory.localization₂ p (M'.map ((f : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) := by
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨s, hs, hsm⟩ := h hm
  exact ⟨s, hs, ⟨s • m, hsm, by simp⟩⟩

theorem hform_smul_right {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (c : 𝓞 E) (x y : Fin n → E) :
    hform σ J x (c • y) = algebraMap (𝓞 E) E c * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_left {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (c : 𝓞 E) (x y : Fin n → E) :
    hform σ J (c • x) y = σ (algebraMap (𝓞 E) E c) * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_add_left {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_zero_left {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    hform σ J 0 y = 0 := by
  simp [hform]

theorem dualSet_le_locP {n : ℕ} (σ : E →+* E) (e : 𝓞 E ≃+* 𝓞 E)
    (he : ∀ t : 𝓞 E, σ (algebraMap (𝓞 E) E t) = algebraMap (𝓞 E) E (e t))
    (J : Matrix (Fin n) (Fin n) E) {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} (hf : Module.Finite (𝓞 E) Λ')
    (I I' : Ideal (𝓞 E)) [I.IsPrime] [I'.IsPrime] (hI : ∀ t, t ∉ I' → e t ∉ I) (h : Λ' ≤ Formalism.HermitianLatticesTheory.localization₂ I' Λ) :
    Formalism.BasicNotions.dualSet σ J Λ ⊆ Formalism.HermitianLatticesTheory.localization₂ I (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet σ J Λ')) := by
  classical
  intro y hy
  obtain ⟨G, hG⟩ := Module.Finite.iff_fg.1 hf
  have ht : ∀ g ∈ G, ∃ t : 𝓞 E, t ∉ I' ∧ t • g ∈ Λ := fun g hg => by
    obtain ⟨t, ht, htg⟩ := h (hG ▸ Submodule.subset_span hg)
    exact ⟨t, ht, htg⟩
  choose! t ht1 ht2 using ht
  refine ⟨∏ g ∈ G, e (t g), fun hmem => ?_, Submodule.subset_span ?_⟩
  · obtain ⟨g, hg, hgI⟩ := (Ideal.IsPrime.prod_mem_iff (p := I)).1 hmem
    exact hI _ (ht1 g hg) hgI
  · intro z hz
    rw [← hG] at hz
    induction hz using Submodule.span_induction with
    | mem g hg =>
      rw [hform_smul_right, ← Finset.mul_prod_erase G _ hg, map_mul, mul_assoc, ← he, mul_left_comm, ← hform_smul_left]
      obtain ⟨r, hr⟩ := hy _ (ht2 g hg)
      rw [← hr, ← map_mul]
      exact ⟨_, rfl⟩
    | zero => rw [hform_zero_left]; exact ⟨0, map_zero _⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨r', hr'⟩ := hx'
      rw [hform_add_left, ← hr, ← hr', ← map_add]
      exact ⟨_, rfl⟩
    | smul c x _ hx =>
      obtain ⟨r, hr⟩ := hx
      rw [hform_smul_left, he, ← hr, ← map_mul]
      exact ⟨_, rfl⟩

end Gen

section SeamT

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (iE : K ≃+* K') {m : ℕ}

theorem algebraMap_mapRingEquiv (t : 𝓞 K) :
    algebraMap (𝓞 K') K' (RingOfIntegers.mapRingEquiv iE t) = iE (algebraMap (𝓞 K) K t) := rfl

theorem exists_of_mem_span_image (N : Submodule (𝓞 K) (Fin m → K)) (z : Fin m → K')
    (hz : z ∈ Submodule.span (𝓞 K') ((fun (x : Fin m → K) (i : Fin m) => iE (x i)) '' (N : Set (Fin m → K)))) :
    ∃ w ∈ N, (fun i => iE (w i)) = z := by
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨w, hw, rfl⟩ := hz; exact ⟨w, hw, rfl⟩
  | zero => exact ⟨0, N.zero_mem, funext fun i => by simp⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨w', hw', rfl⟩ := hz'
    exact ⟨w + w', N.add_mem hw hw', funext fun i => by simp⟩
  | smul c z _ hz =>
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨(RingOfIntegers.mapRingEquiv iE).symm c • w, N.smul_mem _ hw, funext fun i => ?_⟩
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rw [← algebraMap_mapRingEquiv, RingEquiv.apply_symm_apply]

theorem mem_equivOfRingEquiv (P : HeightOneSpectrum (𝓞 K)) (t : 𝓞 K) :
    RingOfIntegers.mapRingEquiv iE t ∈ (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv iE) P).asIdeal ↔
      t ∈ P.asIdeal := by
  simp [HeightOneSpectrum.equivOfRingEquiv, HeightOneSpectrum.comap, Ideal.mem_comap]

theorem le_localized_of_transport (N N₁ : Submodule (𝓞 K) (Fin m → K)) (P : HeightOneSpectrum (𝓞 K))
    (h : Submodule.span (𝓞 K') ((fun (x : Fin m → K) (i : Fin m) => iE (x i)) '' (N₁ : Set (Fin m → K))) ≤
      Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv iE) P).asIdeal
        (Submodule.span (𝓞 K') ((fun (x : Fin m → K) (i : Fin m) => iE (x i)) '' (N : Set (Fin m → K))))) :
    N₁ ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
  intro y hy
  obtain ⟨c, hc, hcy⟩ := h (Submodule.subset_span ⟨y, hy, rfl⟩)
  obtain ⟨w, hw, hwz⟩ := exists_of_mem_span_image iE N _ hcy
  refine ⟨(RingOfIntegers.mapRingEquiv iE).symm c, fun hP => hc ?_, ?_⟩
  · have := (mem_equivOfRingEquiv iE P _).2 hP
    rwa [RingEquiv.apply_symm_apply] at this
  · convert hw using 1
    funext i
    apply iE.injective
    have := congrFun hwz i
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul] at this ⊢
    rw [this, ← algebraMap_mapRingEquiv, RingEquiv.apply_symm_apply]

end SeamT

theorem exists_smul_mem_of_span {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) : ∃ ν : 𝓞 E, ν ≠ 0 ∧ ν • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.FiniteIndexSubgroup.target
  | exact _root_.GlobalTheory.FiniteIndexSubgroup.target
  | (apply _root_.GlobalTheory.FiniteIndexSubgroup.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteIndexSubgroup.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteIndexSubgroup.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteIndexSubgroup.target ..)

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem incl_smul (v : HeightOneSpectrum (𝓞 F)) (s : 𝓞 E) (x : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((s • x) i)) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E s) •
        fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (x i) := by
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, smul_eq_mul]

theorem mem_localization_of_mem_localLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (B : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) B → Submodule.span E (B : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E), (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (x i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v B → ∀ q : HeightOneSpectrum (𝓞 E), q.under (𝓞 F) = v → x ∈ Formalism.HermitianLatticesTheory.localization₂ q.asIdeal B := by
  intro F E _ _ _ _ _ n v B hB hs x hx q hq
  classical
  obtain ⟨ν, hν, hνx⟩ := exists_smul_mem_of_span B hs x
  let J : Ideal (𝓞 E) := B.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
  have hJ : ∀ s, s ∈ J ↔ s • x ∈ B := fun s => Iff.rfl
  have hJ0 : J.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := by
    intro h
    have := Ideal.eq_bot_of_comap_eq_bot h
    have h2 : ν ∈ J := hνx
    rw [this] at h2
    exact hν h2
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime hJ0 v.asIdeal
  obtain ⟨d, hdQ, hdv⟩ : ∃ d ∈ Q, d ∉ v.asIdeal := by
    by_contra h
    push_neg at h
    rw [sup_eq_left.2 (show Q ≤ v.asIdeal from h)] at hQ
    exact v.isPrime.ne_top hQ
  refine ⟨algebraMap (𝓞 F) (𝓞 E) d, fun h => hdv (by rw [← hq]; exact h), ?_⟩
  refine (GlobalTheory.LatLocGlob.latS_local_global F E n B hB).2.1 hs _ fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [incl_smul]
    exact Submodule.smul_mem (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B)
      (⟨_, Subring.subset_closure (Or.inl ⟨⟨_, ⟨algebraMap (𝓞 F) (𝓞 E) d, rfl⟩⟩, rfl⟩)⟩ : intV E w) hx
  · obtain ⟨π, hπ, hπw⟩ : ∃ π ∈ v.asIdeal ^ (UniqueFactorizationMonoid.normalizedFactors (J.comap (algebraMap (𝓞 F) (𝓞 E)))).count v.asIdeal, π ∉ w.asIdeal := by
      by_contra h
      push_neg at h
      haveI := w.isPrime
      have h1 : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le h
      exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h1).symm)
    have h1 : π * d ∈ J.comap (algebraMap (𝓞 F) (𝓞 E)) := by
      rw [hI]; exact Ideal.mul_mem_mul hπ hdQ
    have h2 : algebraMap (𝓞 F) (𝓞 E) π • algebraMap (𝓞 F) (𝓞 E) d • x ∈ B := by
      rw [← mul_smul, ← map_mul]; exact h1
    obtain ⟨t, ht, e⟩ := GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one (E := E) w π hπw
    have h3 : (fun i => Formalism.UG.inclE (F := F) (w.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) π • algebraMap (𝓞 F) (𝓞 E) d • x) i)) ∈
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B := Submodule.subset_span ⟨_, h2, rfl⟩
    have h4 := Submodule.smul_mem (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B) (⟨t, ht⟩ : intV E w) h3
    rw [incl_smul] at h4
    have e2 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) = algebraMap F E (π : F) := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    rw [e2, Subring.smul_def, smul_smul] at h4
    rwa [show ((⟨t, ht⟩ : intV E w) : E ⊗[F] w.adicCompletion F) * _ = 1 from e, one_smul] at h4

end Loc

section Adel
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_locLat_iff_adelic (w : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Module.Finite (𝓞 E) L)
    (z : Fin n → E ⊗[F] w.adicCompletion F) :
    z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w L ↔ (fun i => Formalism.UG.P.afsplitIE w (z i)) ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) L := by
  rw [GlobalTheory.LatticeStabLocal.mem_latS_adele_iff]
  have h1 : (fun i => prV (E := E) w (Formalism.UG.P.afsplitIE w (z i))) = z :=
    funext fun i => Formalism.UG.P.afsplit_prV_IE w _
  constructor
  · intro hz v
    by_cases hv : v = w
    · subst hv; rw [h1]; exact hz
    · rw [show (fun i => prV (E := E) v (Formalism.UG.P.afsplitIE w (z i))) = 0 from
        funext fun i => Formalism.UG.P.afsplit_prV_IE_ne w v hv _]
      exact zero_mem _
  · intro h
    have := h w
    rwa [h1] at this

end Adel

section LocB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_latS_globLat_iff (Lb : Submodule (𝓞 E) (Fin n → E)) (hf : Module.Finite (𝓞 E) Lb)
    (hs : Submodule.span E (Lb : Set (Fin n → E)) = ⊤) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F))
        (Formalism.UG.CS.globLat g Lb) ↔
      ((g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) _) *ᵥ X ∈
        Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb :=
  Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) Lb hf hs g X

theorem globLat_le_localization_globLat (Lb : Submodule (𝓞 E) (Fin n → E)) (hf : Module.Finite (𝓞 E) Lb)
    (hs : Submodule.span E (Lb : Set (Fin n → E)) = ⊤)
    (x x₁ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Q : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hQ : v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)))
    (hx : Formalism.UG.bc (Formalism.UG.prV (E := E) v) x₁ = Formalism.UG.bc (Formalism.UG.prV (E := E) v) x) :
    Formalism.UG.CS.globLat x Lb ≤ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Formalism.UG.CS.globLat x₁ Lb) := by
  have hlat := fun g => Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) Lb hf hs g
  have hfin : ∀ g, Module.Finite (𝓞 E) (Formalism.UG.CS.globLat g Lb) := fun g => Module.Finite.iff_fg.2 (hlat g).fg
  have hq : Q.under (𝓞 F) = v := HeightOneSpectrum.ext hQ.symm
  intro z hz
  refine mem_localization_of_mem_localLattice F E n v _ (hfin x₁) (hlat x₁).span_eq_top z ?_ Q hq
  have hz' : (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (z i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v (Formalism.UG.CS.globLat x Lb) :=
    Submodule.subset_span ⟨z, hz, rfl⟩
  rw [mem_locLat_iff_adelic v _ (hfin x₁), mem_latS_globLat_iff Lb hf hs]
  rw [mem_locLat_iff_adelic v _ (hfin x), mem_latS_globLat_iff Lb hf hs] at hz'
  set X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun i => Formalism.UG.P.afsplitIE v (Formalism.UG.inclE (F := F) (v.adicCompletion F) (z i))
  have hp : ∀ p : HeightOneSpectrum (𝓞 F),
      (fun i => Formalism.UG.prV (E := E) p ((((x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) i)) =
        (fun i => Formalism.UG.prV (E := E) p ((((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) i)) := by
    intro p
    rw [GlobalTheory.LatticeStabLocal.prV_mulVec, GlobalTheory.LatticeStabLocal.prV_mulVec]
    by_cases hpv : p = v
    · subst hpv
      have h1 : ((x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map (Formalism.UG.prV (E := E) p) =
          ((Formalism.UG.bc (Formalism.UG.prV (E := E) p) x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
      have h2 : ((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map (Formalism.UG.prV (E := E) p) =
          ((Formalism.UG.bc (Formalism.UG.prV (E := E) p) x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
      rw [h1, h2, map_inv, map_inv, hx]
    · rw [show (fun i => Formalism.UG.prV (E := E) p (X i)) = 0 from funext fun i => Formalism.UG.P.afsplit_prV_IE_ne v p hpv _,
        Matrix.mulVec_zero, Matrix.mulVec_zero]
  have e : (((x₁⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) = (((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ X) := by
    funext i
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun p => ?_
    rw [map_sub, sub_eq_zero]
    exact congrFun (hp p) i
  rw [e]
  exact hz'

end LocB

section Glue

theorem latAd_eq' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.latAd y Lb = Formalism.UG.CS.globLat y Lb :=
  Submodule.span_eq (Formalism.UG.CS.globLat y Lb)

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {N : ℕ}

theorem latCo_le_locP (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (a : 𝓞 E)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hf : Module.Finite (𝓞 E) Lb) (hs : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (y y₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Q Qc : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hQ : v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) (hQc : v.asIdeal = Qc.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)))
    (e : 𝓞 E ≃+* 𝓞 E) (he : ∀ t : 𝓞 E, (sp.cm.sig : E →+* E) (algebraMap (𝓞 E) E t) = algebraMap (𝓞 E) E (e t))
    (hI : ∀ t, t ∉ Qc.asIdeal → e t ∉ Q.asIdeal)
    (hy : Formalism.UG.bc (Formalism.UG.prV (E := E) v) y₁ = Formalism.UG.bc (Formalism.UG.prV (E := E) v) y) :
    latCo sp J co a y₁ Lb ≤ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (latCo sp J co a y Lb) := by
  have hfin : Module.Finite (𝓞 E) (Formalism.UG.CS.globLat y Lb) :=
    Module.Finite.iff_fg.2 (Formalism.UG.P.global_lattice_isLattice_holds F E (Fin N) Lb hf hs y).fg
  unfold latCo mvL
  refine map_le_locP Q.asIdeal (toLE co) ?_
  unfold compan
  rw [latAd_eq', latAd_eq']
  refine sup_smul_le_locP Q.asIdeal _ (globLat_le_localization_globLat Lb hf hs y₁ y Q v hQ hy.symm) ?_
  exact Submodule.span_le.2 (dualSet_le_locP _ e he J hfin Q.asIdeal Qc.asIdeal hI (globLat_le_localization_globLat Lb hf hs y y₁ Qc v hQc hy))

end Glue

set_option maxHeartbeats 1000000 in

theorem lat_eq : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ p p₁ hp hp₁ hx P
  classical
  set Q : HeightOneSpectrum (𝓞 D.host.E) := seamP t.seam P.1 with hQdef
  have hQS : Q ∈ ssRec t u μ := by
    rw [hQdef, mem_ssRec, ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop).1]
    exact Finset.mem_union_left _ P.2
  set v : HeightOneSpectrum (𝓞 D.host.F) := Q.under (𝓞 D.host.F) with hvdef
  have hQv : v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := rfl
  have hv : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x₁.1 = Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x.1 :=
    hx v ⟨Q, hQS, hQv⟩
  set e : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E) with hedef
  have hee : ∀ t' : 𝓞 D.host.E, e (e t') = t' := fun t' => Subtype.ext (star_star (t' : D.host.E))
  set Qc : HeightOneSpectrum (𝓞 D.host.E) := HeightOneSpectrum.equivOfRingEquiv e Q with hQcdef
  have hmemc : ∀ t' : 𝓞 D.host.E, e t' ∈ Qc.asIdeal ↔ t' ∈ Q.asIdeal := fun t' => mem_equivOfRingEquiv _ Q t'
  have hI : ∀ t', t' ∉ Qc.asIdeal → e t' ∉ Q.asIdeal := fun t' ht hQ => ht (by rw [← hee t']; exact (hmemc _).2 hQ)
  have hfixF : ∀ r : 𝓞 D.host.F, e (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r := by
    intro r
    apply Subtype.ext
    show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) = _
    have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (r : D.host.F) := by
      show algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) = _
      rw [← IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E, IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E]
    rw [h1]
    exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have hQcv : v.asIdeal = Qc.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [hQv]
    ext r
    simp only [Ideal.mem_comap]
    rw [← hmemc, hfixF]
  have he : ∀ t' : 𝓞 D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) (algebraMap (𝓞 D.host.E) D.host.E t') =
      algebraMap (𝓞 D.host.E) D.host.E (e t') := fun t' => rfl
  have hf := ((St j hj).K β).lev.Lb_fin
  have hs := ((St j hj).K β).lev.Lb_span
  have h1 := latCo_le_locP D.sp (gramN D j hj) (A.crd j hj) a _ hf hs x.1 x₁.1 Q Qc v hQv hQcv e he hI hv
  have h2 := latCo_le_locP D.sp (gramN D j hj) (A.crd j hj) a _ hf hs x₁.1 x.1 Q Qc v hQv hQcv e he hI hv.symm
  rw [← hp.lat, ← hp₁.lat] at h1
  rw [← hp.lat, ← hp₁.lat] at h2
  exact le_antisymm (localization_le_of_le_localization₂ _ (le_localized_of_transport t.seam.iE _ _ P.1 h1))
    (localization_le_of_le_localization₂ _ (le_localized_of_transport t.seam.iE _ _ P.1 h2))

end GlobalTheory.TwV.AwayLat
end
end

section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_decoration_agree_below : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := by
  atlas_forward_decl GlobalTheory.TwV.AwayLat.lat_eq
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.FnlAway
open scoped TensorProduct

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}

theorem exists_place {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E} (H : AdTie A dtU a)
    (j : ℕ) (hj : j ≤ D.R.m) (P : t.Pr.vT (t.word u)) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.F), ∃ h : (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal,
      IsOver v (seamP t.seam P.1) ∧ v ∈ plUnder D.host.F (ssRec t u μ) := by
  classical
  obtain ⟨hSS, -⟩ := t.rd_chain u μ
  have hpi : t.Pr.piT (t.word u) ∈ P.1.asIdeal := by
    have h := P.2
    unfold Formalism.L2.Col.Primes.vT Formalism.L2.Col.divs at h
    split_ifs at h with hf
    · simpa using h
    · simp at h
  have hT : ((t.Pr.T (t.word u) : ℕ) : 𝓞 t.X.E) ∈ P.1.asIdeal := by
    rw [← t.pr_ok.piT_norm]
    exact Ideal.mul_mem_right _ _ hpi
  have hTQ : (((St j hj).T : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P.1).asIdeal := by
    rw [H.T_eq j hj, ← t.T_rec u, ← map_natCast (RingOfIntegers.mapRingEquiv t.seam.iE), mem_seamP]
    exact hT
  have hT0 : (((St j hj).T : ℕ) : 𝓞 D.host.F) ≠ 0 := by
    rw [H.T_eq j hj, ← t.T_rec u]
    exact Nat.cast_ne_zero.2 (t.pr_ok.T_prime _).ne_zero
  have hmem : (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ (seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]
    exact hTQ
  let v : HeightOneSpectrum (𝓞 D.host.F) := ⟨(seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)),
    Ideal.IsPrime.comap _, fun h => hT0 (by rw [h] at hmem; exact (Ideal.mem_bot.1 hmem))⟩
  refine ⟨v, hmem, rfl, seamP t.seam P.1, ?_, rfl⟩
  refine (mem_ssRec t u μ P.1).2 ?_
  rw [hSS]
  unfold Sall
  exact Finset.mem_union.2 (Or.inl P.2)

theorem prV_pullV_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (c : GL (Fin N) E) (x x₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : bc (prV (E := E) v) x₁ = bc (prV (E := E) v) x) (y : Fin N → E) (l : Fin N) :
    prV (E := E) v (pullV (F := F) (ratA F c * x₁) y l) = prV (E := E) v (pullV (F := F) (ratA F c * x) y l) := by
  have key : ∀ z : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), prV (E := E) v (pullV (F := F) z y l) =
      ((((bc (prV (E := E) v) z)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ
        fun i => prV (E := E) v (iA F E (y i))) l := by
    intro z
    rw [← map_inv]
    exact RingHom.map_mulVec (prV (E := E) v) _ _ l
  rw [key, key, map_mul, map_mul, h]

theorem mem_latS_of_latCo {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (c : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (hint : ∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) (v : HeightOneSpectrum (𝓞 F)) (y : Fin N → E)
    (hy : y ∈ latCo sp J c a x Lb) :
    (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) y l)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)) :=
  GlobalTheory.T.pulledLatticeVector_mem_dualBaseLatticeCompletion sp J hJ c a x hx Lb hfin hspan hint v y hy

theorem fnl_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N j)), w ∈ p.deco.1.at P.1 → w ∈ p₁.deco.1.at P.1 → p₁.deco.1.f P w = p.deco.1.f P w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin H j hj β x x₁ p p₁ hp hp₁ hag P w hw hw₁
  obtain ⟨v, hTv, hov, hvU⟩ := exists_place H j hj P
  have hxv := hag v hvU
  obtain ⟨s, hs, hsw⟩ := (mem_locP _ _ _).1 hw
  obtain ⟨s', hs', hsw'⟩ := (mem_locP _ _ _).1 hw₁
  have h1 : (s' * s) • w ∈ p.deco.1.N := by rw [mul_smul]; exact Submodule.smul_mem _ _ hsw
  have h2 : (s' * s) • w ∈ p₁.deco.1.N := by rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hsw'
  have hmem : ∀ (y : UA D j hj) (q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β y q →
      ∀ w' ∈ q.deco.1.N, (fun l => prV (E := D.host.E) v (pullV (F := D.host.F) (ratA D.host.F (A.crd j hj) * y.1)
        (fun b => t.seam.iE (w' b)) l)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D j hj) ((St j hj).K β).lev.Lb)) := by
    intro y q hq w' hw'
    have hy : (fun b => t.seam.iE (w' b)) ∈ latCo D.sp (gramN D j hj) (A.crd j hj) a y.1 ((St j hj).K β).lev.Lb := by
      rw [← hq.lat]
      exact Submodule.subset_span ⟨w', hw', rfl⟩
    exact mem_latS_of_latCo D.sp (gramN D j hj) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) (A.crd j hj) a y.1 y.2
      _ ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span ((St j hj).K β).lev.Lb_int v _ hy
  let z : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
      (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D j hj) ((St j hj).K β).lev.Lb)) :=
    ⟨_, hmem x p hp _ h1⟩
  have e1 := hp.fnl P v hTv hov _ h1 z rfl
  have e2 := hp₁.fnl P v hTv hov _ h2 z (by
    funext l
    exact (prV_pullV_congr v (A.crd j hj) x.1 x₁.1 hxv _ l).symm)
  have e3 : p₁.deco.1.f P ((s' * s) • w) = p.deco.1.f P ((s' * s) • w) := e2.trans e1.symm
  rw [p₁.deco.2.f_smul P _ w hw₁, p.deco.2.f_smul P _ w hw] at e3
  haveI hP := P.1.isPrime
  have hu : Ideal.Quotient.mk P.1.asIdeal (s' * s) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun hm => (hP.mem_or_mem hm).elim hs' hs
  exact mul_left_cancel₀ hu e3

end GlobalTheory.TwV.FnlAway

end
end

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N j)), w ∈ p.deco.1.at P.1 → w ∈ p₁.deco.1.at P.1 → p₁.deco.1.f P w = p.deco.1.f P w) := by
  atlas_forward_decl GlobalTheory.TwV.FnlAway.fnl_away
end

section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : SB t μ, (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm ∈ GLint t.X.E (D.R.N j) P.1 ∧
    ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ •
      ((frsF t.sel (t.tup μ) p P).symm (frsF t.sel (t.tup μ) p₁ P w) - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  first | exact @GlobalTheory.FrameAgree.frame_away | exact GlobalTheory.FrameAgree.frame_away | (intros; apply GlobalTheory.FrameAgree.frame_away <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetLoc

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem qOf_ne_zero (P : HeightOneSpectrum (𝓞 E)) : (qOf P : E) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  unfold qOf
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact P.ne_bot

theorem intAt_qOf_pow (P : HeightOneSpectrum (𝓞 E)) (t : ℕ) : IntAt P ((qOf P : E) ^ t) := by
  simpa using IntAt.coe P ((qOf P : 𝓞 E) ^ t)

theorem congr_of_sub_one {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n) (D a k : ℕ) (hak : a + k ≤ D)
    (hg : ∀ z ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (g z - z) ∈ stdAt E n P)
    (y0 x : Sp E n) (hy : ∀ l, IntAt P ((qOf P : E) ^ a * y0 l))
    (hx : ∀ l, IntAt P (((qOf P : E) ^ k)⁻¹ * (x - y0) l)) :
    ∀ l, IntAt P (((qOf P : E) ^ k)⁻¹ * (g x - y0) l) := by
  have hc : (qOf P : E) ≠ 0 := qOf_ne_zero P
  have hxa : ∀ l, IntAt P ((qOf P : E) ^ a * x l) := fun l => by
    have e : (qOf P : E) ^ a * x l = (qOf P : E) ^ a * y0 l + (qOf P : E) ^ (a + k) * (((qOf P : E) ^ k)⁻¹ * (x - y0) l) := by
      simp only [Pi.sub_apply]
      rw [pow_add]
      field_simp
      ring
    rw [e]
    exact (hy l).add ((intAt_qOf_pow P _).mul (hx l))
  have hz : (qOf P : E) ^ a • x ∈ stdAt E n P := (mem_localization_standardLattice P _).2 fun l => by simpa using hxa l
  have h1 := (mem_localization_standardLattice P _).1 (hg _ hz)
  obtain ⟨t, ht⟩ : ∃ t, D = t + (a + k) := ⟨D - (a + k), by omega⟩
  intro l
  have e : ((qOf P : E) ^ k)⁻¹ * (g x - y0) l = ((qOf P : E) ^ k)⁻¹ * (x - y0) l +
      (qOf P : E) ^ t * ((((qOf P : E) ^ D)⁻¹ • (g ((qOf P : E) ^ a • x) - (qOf P : E) ^ a • x)) l) := by
    rw [map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [ht]
    simp only [pow_add]
    field_simp
    ring
  rw [e]
  exact (hx l).add ((intAt_qOf_pow P t).mul (h1 l))

theorem symm_sub_one {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) (D : ℕ) (hk : κ ∈ GLint E n P)
    (hg : ∀ z ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ z - z) ∈ stdAt E n P) :
    ∀ z ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ.symm z - z) ∈ stdAt E n P := by
  intro z hz
  have hk' : ∀ x, κ x ∈ stdAt E n P ↔ x ∈ stdAt E n P := hk
  have hz' : κ.symm z ∈ stdAt E n P := (hk' _).1 (by simpa using hz)
  have h := hg _ hz'
  rw [LinearEquiv.apply_symm_apply] at h
  have e : ((qOf P : E) ^ D)⁻¹ • (κ.symm z - z) = -(((qOf P : E) ^ D)⁻¹ • (z - κ.symm z)) := by
    rw [← smul_neg, neg_sub]
  rw [e]
  exact (stdAt E n P).neg_mem h

end Local

end GlobalTheory.CosetLoc

namespace GlobalTheory.CosetLoc

open Classical in

theorem sameCoset_symm_iff : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) {n : ℕ} (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (y0 : Sp X.E n), cst.Ok →
  κ ∈ GLint X.E n P.1 → (∀ w ∈ stdAt X.E n P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E n P.1) →
  (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) →
  (P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) * y0 l)) → (P.1 ∉ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y0 l)) →
  ∀ w, SameCoset sel mu cst P (κ.symm w) y0 ↔ SameCoset sel mu cst P w y0 := by
  intro X Pr sel S mu cst P n κ y0 hc hk hg hD hy1 hy2 w
  have hg' := symm_sub_one κ (cst.D P) hk hg

  obtain ⟨a, hak, hy⟩ : ∃ a, a + (if P.1 ∈ Pr.vGs then 0 else cst.M) ≤ cst.D P ∧ ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ a * y0 l) := by
    by_cases hP : P.1 ∈ Pr.vGs
    · refine ⟨1, ?_, fun l => by simpa using hy1 hP l⟩
      rw [if_pos hP]
      simpa using hc.D_pos P
    · refine ⟨cst.M, ?_, hy2 hP⟩
      rw [if_neg hP]
      have := hD hP
      omega
  unfold SameCoset
  constructor
  · intro h
    have := congr_of_sub_one κ (cst.D P) a _ hak hg y0 (κ.symm w) hy h
    simpa using this
  · intro h
    exact congr_of_sub_one κ.symm (cst.D P) a _ hak hg' y0 w hy h

end GlobalTheory.CosetLoc
end
end

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sameCouplingCoset_invariant_frame_congruent_one : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) {n : ℕ} (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (y0 : Sp X.E n), cst.Ok →
  κ ∈ GLint X.E n P.1 → (∀ w ∈ stdAt X.E n P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E n P.1) →
  (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) →
  (P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) * y0 l)) → (P.1 ∉ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y0 l)) →
  ∀ w, SameCoset sel mu cst P (κ.symm w) y0 ↔ SameCoset sel mu cst P w y0 := by
  atlas_forward_decl GlobalTheory.CosetLoc.sameCoset_symm_iff
end

section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepDatum_typePrime_invariant_frames_congruent_one : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  first | exact @GlobalTheory.TwV.AwayTopG.topDat_frames_vGs | exact GlobalTheory.TwV.AwayTopG.topDat_frames_vGs | (intros; apply GlobalTheory.TwV.AwayTopG.topDat_frames_vGs <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepDatum_twistPrime_invariant_congruentFrames : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  first | exact @GlobalTheory.TopFrameQ.topDat_frames_tie | exact GlobalTheory.TopFrameQ.topDat_frames_tie | (intros; apply GlobalTheory.TopFrameQ.topDat_frames_tie <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.AwayTop

theorem inFr_trans {E : Type} [Field E] {n m : ℕ} (f f₁ : Sp E n ≃ₗ[E] Sp E n) (g g₁ : Sp E m ≃ₗ[E] Sp E m) (z : HomE E n m) :
    inFr f₁ g₁ z = (g₁.trans g.symm).symm.toLinearMap ∘ₗ inFr f g z ∘ₗ (f₁.trans f.symm).toLinearMap := by
  refine LinearMap.ext fun w => ?_
  simp [inFr, LinearEquiv.trans_symm]

theorem symm_trans_symm {E : Type} [Field E] {n : ℕ} (f f₁ : Sp E n ≃ₗ[E] Sp E n) (y : Sp E n) :
    f₁.symm y = (f₁.trans f.symm).symm (f.symm y) := by
  simp [LinearEquiv.trans_symm]

theorem ptAway_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i = t.m2 + 1 → PtAway A a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi hi1
  subst hi1
  intro β β' x x' x₁ x₁' p p' p₁ p₁' h1 h2 h3 h4 hag
  have hagS : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 :=
    fun v hv => (hag v hv).1
  have hagT : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1 :=
    fun v hv => (hag v hv).2
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have e : ∀ q q', xiPt A (t.m2 + 1) hi β β' q q' =
      XiTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) q (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) q' := by
    intro q q'
    funext z
    unfold xiPt
    rw [dif_neg (by omega), if_neg (by omega)]
  rw [e, e]

  have hF := GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS
  have hF' := GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT

  have hcos : cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁ = cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p := by
    ext y
    simp only [cosetOf, Set.mem_setOf_eq]
    refine forall_congr' fun P => ?_
    have hb := GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist A dtU a hP hTie (Nat.le_of_succ_le hi) β P (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
      ((GlobalTheory.TwU.Model.sameCoset_equiv t.sel (t.tup μ) (t.cst μ) P).refl _)
    have key := GlobalTheory.T.sameCouplingCoset_invariant_frame_congruent_one t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm)
      (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) hc (hF P).1 (hF P).2 (hok.depthQ P) hb.1 hb.2 ((frsF t.sel (t.tup μ) p P).symm y)
    rw [← symm_trans_symm] at key
    exact key
  rw [hcos]
  funext z
  rw [XiTop_eq, XiTop_eq]
  congr 1
  ·
    unfold phiT
    congr 1
    refine propext (forall_congr' fun P => ?_)
    have hA := GlobalTheory.T.point_decoration_agree_below A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS P
    have hA' := GlobalTheory.T.point_decoration_agree_below A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT P
    have hB := GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS P
    have hB' := GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT P
    rw [hA, hA']
    refine forall_congr' fun w => imp_congr_right fun hw => and_congr_right fun hzw => ?_
    rw [hB w hw (hA ▸ hw), hB' _ hzw (hA' ▸ hzw)]
  ·
    refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_vector_prescribed_cosets_badPrimes_frames t.sel (t.tup μ) (t.cst μ) (frsF t.sel (t.tup μ) p) (fun P => y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
    have hrep : repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p :=
      Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) ⟨r, hr⟩
    have hb := GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist A dtU a hP hTie (Nat.le_of_succ_le hi) β P _ (hrep P)
    rw [inFr_trans (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p₁ P) (frsF t.sel (t.tup μ) p' P) (frsF t.sel (t.tup μ) p₁' P) z,
      symm_trans_symm (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p₁ P)]
    by_cases hG : P.1 ∈ t.Pr.vGs
    · exact GlobalTheory.T.lastStepDatum_typePrime_invariant_frames_congruent_one A dtU a hP hTie P hG _ _ (hF P).1 (hF P).2 (hF' P).1 (hF' P).2 _ _ (hb.1 hG)
    · exact GlobalTheory.T.lastStepDatum_twistPrime_invariant_congruentFrames A dtU a hP hTie P hG _ _ (hF P).1 (hF P).2 (hF' P).1 (hF' P).2 _ _ (hb.2 hG)

end GlobalTheory.TwV.AwayTop

end
end
