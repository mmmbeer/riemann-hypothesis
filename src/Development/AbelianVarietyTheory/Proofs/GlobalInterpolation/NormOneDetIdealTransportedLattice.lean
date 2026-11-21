import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ScalarCharacterTwist
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CharacterValuation
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LiesOverSpanOfNatCastMemHeightOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpNegOneLtOne

open NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

namespace GlobalTheory.CharValCompare

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke

section Pull

variable {E E' : Type} [Field E] [Field E'] (e : E ≃+* E')

theorem map_osmul (c : 𝓞 E) (a : E) : e (c • a) = RingOfIntegers.mapRingEquiv e c • e a := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

def pull (I : Submodule (𝓞 E') E') : Submodule (𝓞 E) E where
  carrier := {x | e x ∈ I}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show e (a + b) ∈ I
    rw [map_add]; exact add_mem ha hb
  smul_mem' := fun c a ha => by
    show e (c • a) ∈ I
    rw [map_osmul]
    exact I.smul_mem _ ha

theorem mem_pull (I : Submodule (𝓞 E') E') (x : E) : x ∈ pull e I ↔ e x ∈ I := Iff.rfl

theorem pull_one : pull e 1 = 1 := by
  ext x
  rw [mem_pull, Submodule.mem_one, Submodule.mem_one]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨RingOfIntegers.mapRingEquiv e.symm r, by rw [← e.symm_apply_apply x, ← hr]; rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e r, rfl⟩

theorem pull_norm (c : E → E) (c' : E' → E') (h : ∀ x, e (c x) = c' (e x)) {I : Submodule (𝓞 E') E'}
    (hI : ∃ J : Submodule (𝓞 E') E', (∀ x, x ∈ J ↔ c' x ∈ I) ∧ I * J = 1) :
    ∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ c x ∈ pull e I) ∧ pull e I * J = 1 := by
  obtain ⟨J, hJ, hIJ⟩ := hI
  refine ⟨pull e J, fun x => by rw [mem_pull, mem_pull, hJ, h], le_antisymm ?_ ?_⟩
  · rw [Submodule.mul_le]
    intro x hx y hy
    rw [← pull_one e, mem_pull, map_mul, ← hIJ]
    exact Submodule.mul_mem_mul hx hy
  · rw [Submodule.one_le]
    have h1 : ∀ z ∈ I * J, e.symm z ∈ pull e I * pull e J := by
      intro z hz
      refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) fun a b ha hb => by rw [map_add]; exact add_mem ha hb
      rw [map_mul]
      exact Submodule.mul_mem_mul (by simpa [mem_pull] using ha) (by simpa [mem_pull] using hb)
    simpa using h1 1 (hIJ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩)

end Pull

section Vp

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mem_vpIdeal (P : HeightOneSpectrum (𝓞 E)) (x : E) : x ∈ CharacterValuation.vpIdeal P ↔
    ∀ y ∈ (conjPrime₂ P).asIdeal, ∃ z ∈ P.asIdeal, algebraMap (𝓞 E) E z = algebraMap (𝓞 E) E y * x := by
  have h0 : (((conjPrime₂ P).asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 (conjPrime₂ P).ne_bot
  unfold CharacterValuation.vpIdeal
  rw [FractionalIdeal.mem_coe, ← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero h0]
  constructor
  · intro h y hy
    have := h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, rfl⟩)
    rw [mul_comm] at this
    exact (FractionalIdeal.mem_coeIdeal _).1 this
  · intro h y hy
    obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    rw [mul_comm]
    exact (FractionalIdeal.mem_coeIdeal _).2 (h z hz)

theorem star_mem_vpIdeal {P : HeightOneSpectrum (𝓞 E)} {x : E} (h : x ∈ CharacterValuation.vpIdeal P) : star x ∈ CharacterValuation.vpIdeal (conjPrime₂ P) := by
  rw [mem_vpIdeal] at h ⊢
  intro y hy
  rw [conjP_conjP] at hy
  obtain ⟨z, hz, e⟩ := h (cO E y) (by rwa [mem_conjP, cO_cO])
  refine ⟨cO E z, by rwa [mem_conjP, cO_cO], ?_⟩
  rw [algebraMap_cO, e, star_mul', algebraMap_cO, star_star]

theorem normOne_vpIdeal (P : HeightOneSpectrum (𝓞 E)) : NormOne (CharacterValuation.vpIdeal P) := by
  refine ⟨CharacterValuation.vpIdeal (conjPrime₂ P), fun x => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · have := star_mem_vpIdeal h
    rwa [conjP_conjP] at this
  · have := star_mem_vpIdeal h
    rwa [star_star] at this
  · have h0 : (((conjPrime₂ P).asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 (conjPrime₂ P).ne_bot
    have h1 : ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 P.ne_bot
    unfold CharacterValuation.vpIdeal
    rw [conjP_conjP, ← FractionalIdeal.coe_mul, mul_mul_mul_comm, ← mul_inv, mul_comm ((conjPrime₂ P).asIdeal : FractionalIdeal (𝓞 E)⁰ E),
      mul_inv_cancel₀ (mul_ne_zero h1 h0), FractionalIdeal.coe_one]

theorem isSdLat_vpLat (P : HeightOneSpectrum (𝓞 E)) : IsSdLat (CharacterValuation.vpLat P) := self_dual_rank_one_lattice (normOne_vpIdeal P)

omit [StarRing E] in

theorem isFrames_iff {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} (N : Submodule (𝓞 E) (Sp E n)) (fr : Frs E n SB) :
    CharacterValuation.IsFrames N fr ↔ ScalarCharacterTwist.FrOf N fr := Iff.rfl

end Vp

section Val

variable {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)

omit [NumberField K] in
theorem sig_desc {z : ℂ} (h : ∃ k, σ k = z) : σ (desc σ z) = z := by
  unfold desc
  rw [dif_pos h]
  exact h.choose_spec

omit [NumberField K] in
theorem desc_sig (k : K) : desc σ (σ k) = k := σ.injective (sig_desc σ ⟨k, rfl⟩)

theorem unit_iff (w : HeightOneSpectrum (𝓞 K)) (k : K) : ScalarCharacterTwist.UnitAtW σ w (σ k) ↔ CharacterValuation.UnitAt w k :=
  ScalarCharacterTwist.unitAtW_iff σ w k

end Val

section Chi

variable {D : D7} {X : Fields} (s : Seam D X) {χ : TaylorLogMetric.IdE D → ℂ}

theorem idTo_eq (I : Submodule (𝓞 X.E) X.E) : CharacterValuation.idTo s I = pull s.iE.symm I := by
  have : s.iE '' (I : Set X.E) = (pull s.iE.symm I : Set D.host.E) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [mem_pull] using hx
    · intro hy
      exact ⟨_, hy, s.iE.apply_symm_apply y⟩
  rw [CharacterValuation.idTo, this, Submodule.span_eq]

theorem mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) :
    y ∈ s.lat N ↔ (fun i => s.iE.symm (y i)) ∈ N := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      simpa using hx
    | zero =>
      convert N.zero_mem using 1
      funext i
      exact map_zero _
    | add a b _ _ ha hb =>
      convert N.add_mem ha hb using 1
      funext i
      exact map_add _ _ _
    | smul c a _ ha =>
      convert N.smul_mem (RingOfIntegers.mapRingEquiv s.iE.symm c) ha using 1
      funext i
      exact map_osmul s.iE.symm c (a i)
  · intro hy
    exact Submodule.subset_span ⟨_, hy, funext fun i => s.iE.apply_symm_apply _⟩

theorem detId_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N) = pull s.iE.symm (detI N) := by
  apply le_antisymm
  · rw [TaylorLogMetric.detId, Submodule.span_le]
    rintro _ ⟨A, hA, rfl⟩
    refine Submodule.subset_span ⟨A.map s.iE.symm, fun v hv => ?_, (s.iE.symm : D.host.E →+* X.E).map_det A⟩
    have h1 := (mem_lat s N _).1 (hA (fun i => s.iE (v i)) fun i _ => by
      have := hv i (Set.mem_univ _)
      rw [← pull_one s.iE] at this
      exact this)
    convert h1 using 1
    funext i
    simp [Matrix.mulVec, dotProduct]
  · have : detI N ≤ pull s.iE (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
      rw [detI, Submodule.span_le]
      rintro _ ⟨A, hA, rfl⟩
      refine Submodule.subset_span ⟨A.map s.iE, fun v hv => (mem_lat s N _).2 ?_, (s.iE : X.E →+* D.host.E).map_det A⟩
      have h1 := hA (fun i => s.iE.symm (v i)) fun i _ => by
        have := hv i (Set.mem_univ _)
        rw [← pull_one s.iE.symm] at this
        exact this
      convert h1 using 1
      funext i
      simp [Matrix.mulVec, dotProduct]
    intro y hy
    simpa [mem_pull] using this hy

variable {s}

theorem normOne_idealPreimageUnderRingEquiv (hs : s.Ok) {I : Submodule (𝓞 X.E) X.E} (h : NormOne I) : TaylorLogMetric.N1 D (pull s.iE.symm I) :=
  pull_norm s.iE.symm D.host.conj star (fun x => by rw [RingEquiv.symm_apply_eq, hs.2, s.iE.apply_symm_apply]) h

theorem normOne_detIdeal_transportedLattice (hs : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
  rw [detId_lat]
  exact normOne_idealPreimageUnderRingEquiv hs (normOne_detI hN)

theorem char_det_rank_one_lattice (I : Submodule (𝓞 X.E) X.E) : CharacterValuation.chiDet s χ (lat1 I) = CharacterValuation.chiK s χ (pull s.iE.symm I) := by
  rw [CharacterValuation.chiDet, detId_lat, det_ideal_rank_one_lattice]

theorem chiVp_eq (P : HeightOneSpectrum (𝓞 X.E)) : CharacterValuation.chiVp s χ P = CharacterValuation.chiDet s χ (CharacterValuation.vpLat P) := by
  rw [CharacterValuation.chiVp, idTo_eq]
  exact (char_det_rank_one_lattice _).symm

end Chi

section Parts

variable {D : D7} {Z : Dat} {s : Seam D Z.X} {χ : TaylorLogMetric.IdE D → ℂ}
  {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ}
  {mu : Tup Z.X.F Z.X.E Z.X.K S} {cst : LocCst Z.X (rowSG Z.Pr sel mu)}

theorem piT_ne_zero (hZ : Z.Ok) (u : Z.Pr.Word) : Z.Pr.piT u ≠ 0 := by
  intro h
  have h1 := hZ.primes.piT_norm u
  rw [h, zero_mul] at h1
  exact (hZ.primes.T_prime u).ne_zero (by exact_mod_cast h1.symm)

theorem T_mem (hZ : Z.Ok) {u : Z.Pr.Word} {P : HeightOneSpectrum (𝓞 Z.X.E)} (hP : P ∈ Z.Pr.vT u) :
    ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∈ P.asIdeal := by
  rw [← hZ.primes.piT_norm u]
  exact Ideal.mul_mem_right _ _ (decoFin_mem_of_mem_divs hP)

theorem T_eq (hZ : Z.Ok) (u : Z.Pr.Word) (τ : Z.X.Tau) :
    ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) = Z.X.embO τ (Z.Pr.piT u) * Z.X.embO τ (Z.X.conjO (Z.Pr.piT u)) := by
  rw [← map_mul, hZ.primes.piT_norm u, map_natCast]

theorem seenC_iff (hZ : Z.Ok) {u : Z.Pr.Word} {P : HeightOneSpectrum (𝓞 Z.X.E)} (hP : P ∈ Z.Pr.vT u) (w : HeightOneSpectrum (𝓞 Z.X.K)) :
    seenC Z.Pr u w ↔ ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal ∧ ∃ τ, SeesP w τ P := by
  constructor
  · intro h
    obtain ⟨τ₀⟩ : Nonempty Z.X.Tau := Fintype.card_pos_iff.1 hZ.fields.f_pos
    have hT : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal := by
      rw [T_eq hZ u τ₀]
      exact Ideal.mul_mem_right _ _ (h τ₀)
    obtain ⟨τ, h1 | h1⟩ := GlobalTheory.exists_comap_eq_or_eq_conj Z.X hZ.fieldsConditions _ (hZ.primes.T_prime u) w P hT (T_mem hZ hP)
    · exact ⟨hT, τ, h1⟩
    · have h2 : Z.Pr.piT u ∈ (pullW τ w).asIdeal := h τ
      rw [show pullW τ w = conjPrime₂ P from h1] at h2
      exact absurd h2 (conj_piT_notMem hZ.primes u ⟨P, hP⟩)
  · rintro ⟨_, τ, h⟩ τ'
    have h2 : Z.Pr.piT u ∈ (pullW τ w).asIdeal := by
      rw [show pullW τ w = P from h]
      exact decoFin_mem_of_mem_divs hP
    have h3 : Z.X.embO τ' (Z.Pr.piT u) = Z.X.embO τ (Z.Pr.piT u) := RingOfIntegers.ext (hZ.primes.piT_Kq u τ' τ)
    rw [h3]
    exact h2

theorem mu_offset_rank_one_lattice (SB : Finset (HeightOneSpectrum (𝓞 Z.X.E))) (mU : HeightOneSpectrum (𝓞 Z.X.E) → Z.X.Kˣ) {n : ℕ}
    {N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)} (hN : IsSdLat N) : muOff sel SB mU (lat1 (detI N)) = muOff sel SB mU N := by
  unfold muOff
  simp only [order_det_rank_one_lattice _ hN.1]

theorem mu_inverse_rank_one_lattice (i : ℕ) {n : ℕ} {N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)} (hN : IsSdLat N) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) :
    CharacterValuation.muInv Z sel mu cst i (lat1 (detI N)) (fun P => detFr (fr P)) = CharacterValuation.muInv Z sel mu cst i N fr := by
  unfold CharacterValuation.muInv muInvDet
  simp only [mu_offset_rank_one_lattice _ _ hN, det_detFr]

theorem chiDet_detI {n : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) :
    CharacterValuation.chiDet s χ (lat1 (detI N)) = CharacterValuation.chiDet s χ N := by
  rw [char_det_rank_one_lattice, CharacterValuation.chiDet, detId_lat]

theorem unit_chiF {w : HeightOneSpectrum (𝓞 Z.X.K)} {x y : Z.X.K} (hx : CharacterValuation.UnitAt w x) (hy : CharacterValuation.UnitAt w y) (a b : ℤ) :
    CharacterValuation.UnitAt w (x ^ a * y ^ b) := by
  unfold CharacterValuation.UnitAt at *
  rw [map_mul, map_zpow₀, map_zpow₀, hx, hy, one_zpow, one_zpow, one_mul]

theorem unit_scal {w : HeightOneSpectrum (𝓞 Z.X.K)} {x y : Z.X.K} (hx : w.valuation Z.X.K x = 1) (hy : w.valuation Z.X.K y = 1) :
    w.valuation Z.X.K (x * y⁻¹) = 1 := by
  rw [map_mul, map_inv₀, hx, hy, inv_one, one_mul]

theorem exists_frames (SB : Finset (HeightOneSpectrum (𝓞 Z.X.E))) {n : ℕ} {N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)} (hN : IsSdLat N) :
    ∃ fr : Frs Z.X.E n SB, ScalarCharacterTwist.FrOf N fr := by
  choose f hf using fun P : SB => exists_isFr P.1 hN.1
  exact ⟨f, hf⟩

theorem exists_isSel (X : Fields) : ∃ sel, IsSel X sel := by
  have : ∀ v : HeightOneSpectrum (𝓞 X.F), ∃ P : HeightOneSpectrum (𝓞 X.E), P.asIdeal.under (𝓞 X.F) = v.asIdeal := by
    intro v
    have := v.isMaximal
    obtain ⟨Q, hQ, h⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.E) v.asIdeal (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 X.F) (𝓞 X.E))]
      exact bot_le)
    exact ⟨⟨Q, hQ.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField _)⟩, h⟩
  choose f hf using this
  exact ⟨f, hf⟩

theorem exists_cst (hZ : Z.Ok) {m0 : Fin Z.R.m → Formalism.L2.Host.HChar Z.X.E} {eta : Formalism.L2.Host.HChar Z.X.E}
    (h : Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta)
    (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (mu : Tup Z.X.F Z.X.E Z.X.K S) :
    ∃ cst : LocCst Z.X (rowSG Z.Pr sel mu), MuqTieG (Pr := Z.Pr) (R := Z.R) sel mu cst Z.sig0 m0 := by
  choose f hf using GlobalTheory.TameVal.locK_mem_coeff Z hZ m0 eta h
  have hq : ∀ P : HeightOneSpectrum (𝓞 Z.X.E), ((Formalism.L2.Col.qOf P : ℕ) : Z.X.E) ≠ 0 := fun P => by
    have : Ideal.absNorm P.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact P.ne_bot
    exact_mod_cast this
  refine ⟨⟨fun _ _ => 1, fun _ => 1, fun _ => 1, fun j P => if h : j - 1 < Z.R.m then
    (f ⟨j - 1, h⟩ P.1 (Units.mk0 _ (hq P.1)))⁻¹ * (((qVal (mu : Chr Z.X.F Z.X.E Z.X.K) P.1)⁻¹ : Z.X.Kˣ) : Z.X.K) else 0,
    0, 0, 0, false⟩, fun i hi P _ qu hqu => ?_⟩
  obtain rfl : qu = Units.mk0 _ (hq P.1) := Units.ext hqu
  have hi' : i + 1 - 1 < Z.R.m := hi
  simp only [dif_pos hi']
  rw [map_mul, map_inv₀, hf]
  rfl

end Parts

end GlobalTheory.CharValCompare
