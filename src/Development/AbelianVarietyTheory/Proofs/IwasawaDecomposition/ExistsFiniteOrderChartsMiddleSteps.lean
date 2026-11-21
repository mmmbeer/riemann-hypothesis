import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelConjBaseLatticeUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitLocalLevelFirstFactorReadsComponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointUnitaryNormalisesLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Formalism.LocalToGlobal.Columns.ChainTwFin
import Formalism.LocalToGlobal.Columns.QthPrincInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetMovesWithFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetsInFramesEqIffReductions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepPointGivenReductionsCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfPow
import Formalism.LocalToGlobal.Columns.ThetaOpenTwLevQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimes

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem lamExp_of_princ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (hN : 0 < N) (H : Subgroup ↥(GLint E n P)) (lam : ↥H →* Kˣ)
    (hH : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ H, lam ⟨g, h⟩ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : ↥H, lam x ^ m = 1 := by
  set L : Subgroup ↥(GLint E n P) := lam.ker.map H.subtype with hL
  have hfin : Finite (↥(GLint E n P) ⧸ L) := tfFinite_of_princ P N hN L fun g hg =>
    ⟨⟨g, (hH g hg).choose⟩, (hH g hg).choose_spec, rfl⟩
  have hLi : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hrel := Subgroup.relIndex_mul_index hLH
  have hsub : L.subgroupOf H = lam.ker := Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hki : lam.ker.index ≠ 0 := by
    intro h0
    apply hLi
    rw [← hrel, Subgroup.relIndex, hsub, h0, zero_mul]
  refine ⟨lam.ker.index, Nat.pos_of_ne_zero hki, fun x => ?_⟩
  have := Subgroup.pow_index_mem lam.ker x
  rw [MonoidHom.mem_ker, map_pow] at this
  exact this

theorem qbLoc_chr_exp {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q) (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ) (P : Q) : ∃ m : ℕ, 0 < m ∧ ∀ k, (qbLoc hc Θ hQ hΘ).chr P k ^ m = 1 := by
  obtain ⟨N, hN, hH⟩ := hΘ P
  obtain ⟨m, hm, hx⟩ := lamExp_of_princ P.1 N hN (Θ P).H (Θ P).lam hH
  exact ⟨m, hm, fun k => hx _⟩

end GlobalTheory.Mem.Col2.ChEx
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLevelCharacter_finiteOrder : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q) (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ) (P : Q), ∃ m : ℕ, 0 < m ∧ ∀ k, (qbLoc hc Θ hQ hΘ).chr P k ^ m = 1 := by
  atlas_forward_decl GlobalTheory.Mem.Col2.ChEx.qbLoc_chr_exp
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section CutOpen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

omit [StarRing E] in
theorem intAt_iff_val_le_one {P : HeightOneSpectrum (𝓞 E)} {a : E} : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  intro h
  obtain ⟨r, s, hs⟩ := P.exists_primeCompl_mul_eq_of_integer a h
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hs⟩

theorem mem_stdAt_iff_val (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ stdAt E n P ↔ ∀ i, P.valuation E (x i) ≤ 1 := by
  rw [ciMem_stdAt]
  exact forall_congr' fun _ => intAt_iff_val_le_one

theorem lqPrinc_mono {P : HeightOneSpectrum (𝓞 E)} {N N' : ℕ} (h : N ≤ N') {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : lqPrinc P N' g) : lqPrinc P N g := by
  intro i j
  refine (hg i j).trans ?_
  change WithZero.exp (-(N' : ℤ)) ≤ WithZero.exp (-(N : ℤ))
  rw [WithZero.exp_le_exp]
  omega

theorem smul_sub_mem_of_princ {P : HeightOneSpectrum (𝓞 E)} {N a : ℕ} (g : ↥(GLint E n P))
    (hg : lqPrinc P (N + a) (g : Sp E n ≃ₗ[E] Sp E n)) {c : E} {z : Sp E n}
    (ha : ∀ j, P.valuation E (c⁻¹ * z j) ≤ WithZero.exp (a : ℤ)) {x : Sp E n}
    (hx : c⁻¹ • (x - z) ∈ stdAt E n P) : c⁻¹ • ((g : Sp E n ≃ₗ[E] Sp E n) x - z) ∈ stdAt E n P := by
  set f : Sp E n ≃ₗ[E] Sp E n := g.1 with hf
  have hgw : f (c⁻¹ • (x - z)) ∈ stdAt E n P := (g.2 _).2 hx
  have hsplit : c⁻¹ • (f x - z) = f (c⁻¹ • (x - z)) + c⁻¹ • (f z - z) := by
    rw [map_smul, map_sub, smul_sub, smul_sub, smul_sub]
    abel
  rw [hsplit]
  refine (stdAt E n P).add_mem hgw ?_
  rw [mem_stdAt_iff_val]
  intro i
  have hfz : f z - z = (LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) *ᵥ z := by
    rw [Matrix.sub_mulVec, LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]
    rfl
  have e : (c⁻¹ • (f z - z)) i = ∑ j, (LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) i j * (c⁻¹ * z j) := by
    rw [hfz, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  calc P.valuation E ((LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) i j) * P.valuation E (c⁻¹ * z j)
      ≤ WithZero.exp (-((N + a : ℕ) : ℤ)) * WithZero.exp (a : ℤ) := mul_le_mul' (hg i j) (ha j)
    _ = WithZero.exp (-(N : ℤ)) := by rw [← WithZero.exp_add]; congr 1; push_cast; ring
    _ ≤ 1 := by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem thetaOpen_cutQ {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q) (hΘ : ThetaOpen Θ)
    (C : ∀ P : Q, Set (Sp E n))
    (hC : ∀ P : Q, C P = ∅ ∨ ∃ (z : Sp E n) (c : E), c ≠ 0 ∧ C P = {x | c⁻¹ • (x - z) ∈ stdAt E n P.1}) :
    ThetaOpen (cutQ Θ C) := by
  intro P
  obtain ⟨N, hN, hT⟩ := hΘ P
  have hstab : ∃ N' : ℕ, N ≤ N' ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 N' (g : Sp E n ≃ₗ[E] Sp E n) →
      g ∈ frStab P.1 (C P) := by
    rcases hC P with h | ⟨z, c, _, h⟩
    · refine ⟨N, le_rfl, fun g _ => ?_⟩
      rw [mem_frStab, h]
      intro v
      simp
    · obtain ⟨a, ha⟩ := qth_bound P.1 (Matrix.of fun (_ j : Fin n) => c⁻¹ * z j)
      have ha' : ∀ j, P.1.valuation E (c⁻¹ * z j) ≤ WithZero.exp (a : ℤ) := fun j => by
        simpa using ha j j
      refine ⟨N + a, by omega, fun g hg => ?_⟩
      rw [mem_frStab, h]
      intro v
      show c⁻¹ • (g.1 v - z) ∈ stdAt E n P.1 ↔ c⁻¹ • (v - z) ∈ stdAt E n P.1
      constructor
      · intro hv
        have hi := smul_sub_mem_of_princ g⁻¹ (qth_princ_inv P.1 g hg) ha' hv
        have e : ((g⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) (g.1 v) = v := LinearEquiv.symm_apply_apply g.1 v
        rwa [e] at hi
      · exact smul_sub_mem_of_princ g hg ha'
  obtain ⟨N', hNN, hS⟩ := hstab
  refine ⟨N', by omega, fun g hg => ?_⟩
  obtain ⟨hH, hl⟩ := hT g (lqPrinc_mono hNN hg)
  exact ⟨⟨hH, hS g hg⟩, hl⟩

end CutOpen

end GlobalTheory.Mem.Col2.ChEx
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openLevel_cutByCosetStabiliser : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q), ThetaOpen Θ → ∀ (C : ∀ P : Q, Set (Sp E n)), (∀ P : Q, C P = ∅ ∨ ∃ (z : Sp E n) (c : E), c ≠ 0 ∧ C P = {x | c⁻¹ • (x - z) ∈ stdAt E n P.1}) → ThetaOpen (GlobalTheory.Mem.Col2.ChEx.cutQ Θ C) := by
  atlas_forward_decl GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem dc_mul_inv_bij {G : Type} [Group G] (Γ K K' : Subgroup G) (b : G) (hK : ∀ x, x ∈ K' ↔ b⁻¹ * x * b ∈ K)
    {ι : Type} (z : ι → G) (hz : Function.Bijective fun i => (Quotient.mk'' (z i) : ClassSet Γ K)) :
    Function.Bijective fun i => (Quotient.mk'' (z i * b⁻¹) : ClassSet Γ K') := by
  constructor
  · intro i j hij
    obtain ⟨h, hh, k, hk, e⟩ := (DoubleCoset.eq Γ K' _ _).1 hij
    refine hz.1 ((DoubleCoset.eq Γ K _ _).2 ⟨h, hh, b⁻¹ * k * b, (hK k).1 hk, ?_⟩)
    calc z j = (z j * b⁻¹) * b := by group
      _ = h * z i * (b⁻¹ * k * b) := by rw [e]; group
  · intro w
    induction w using Quotient.inductionOn' with
    | h x =>
      obtain ⟨i, hi⟩ := hz.2 (Quotient.mk'' (x * b))
      obtain ⟨h, hh, k, hk, e⟩ := (DoubleCoset.eq Γ K _ _).1 hi
      refine ⟨i, (DoubleCoset.eq Γ K' _ _).2 ⟨h, hh, b * k * b⁻¹, (hK _).2 ?_, ?_⟩⟩
      · have : b⁻¹ * (b * k * b⁻¹) * b = k := by group
        rw [this]
        exact hk
      · calc x = (x * b) * b⁻¹ := by group
          _ = (h * z i * k) * b⁻¹ := by rw [e]
          _ = h * (z i * b⁻¹) * (b * k * b⁻¹) := by group

theorem mem_range_qdStab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}
    (H : Subgroup (GLG E n SG)) (p : DecoF E n ST SG Q) (γ : URat hc n) :
    γ ∈ (qdStab (hc := hc) (Θ := Θ) H p).range ↔ ∃ g : UF E n × H × Θ.grp, ufGL E n g.1 = γ.1 ∧ g • p = p := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a.1, ?_, a.2⟩
    rw [← qdf_ratHom_stab (hc := hc) H p a, ha, ufGL_ratHom]
  · rintro ⟨g, hg1, hg2⟩
    refine ⟨⟨g, hg2⟩, (ratHom_bijective hc n).1 ?_⟩
    rw [qdf_ratHom_stab (hc := hc) H p ⟨g, hg2⟩]
    exact ufGL_inj hc n (hg1.trans (ufGL_ratHom hc n γ).symm)

theorem chartQ_exists : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) {π : 𝓞 E} {T f : ℕ} (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal) (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG) (hidx : (baseLb E n ST).toAddSubgroup.relIndex (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f)) (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) →* ℂˣ) {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hO : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ) (b : GL (Fin n) (AfE F E)) (hbU : b ∈ UAd hc n) (hbV : ∀ v, bc (prV (E := E) v) b ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) (hbL : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, b.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) (hbT : ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)) (hbO : ∀ v, v ∉ badQ' (F := F) SG Q → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1) (bad : Set (HeightOneSpectrum (𝓞 F))) (hb : bad = badQ' (F := F) SG Q) {cl : Type} (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin n → E)) (s : cl → DecoF E n ST SG Q) (y : cl → GL (Fin n) (AfE F E)) (hy : ∀ c, y c ∈ UAd hc n) (hd : ∀ c, FrOver q (y c) (s c)) (hs : Function.Bijective fun c => (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ)) (hlat : ∀ c, lat c = (s c).deco.1.L) (st : ∀ c, stab c →* GL (Fin n) E) (hinj : ∀ c, Function.Injective (st c)) (hr : ∀ c γ, γ ∈ (st c).range ↔ ∃ g : UF E n × ↥(Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) × ↥Θ.grp, ufGL E n g.1 = γ ∧ g • s c = s c) (hchr : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ k, q.chr P k ^ m = 1), ∃ (lev : StepLevel F E hc.sig J T f bad) (Y : cl → UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (SI : ∀ c, stab c →* UJ (hc.sig : E →+* E) J), Function.Bijective (fun c => (Quotient.mk'' (Y c) : Cls lev)) ∧ (∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F), x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔ ((Y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb) ∧ (∀ c, Function.Injective (SI c)) ∧ (∀ c (γ : UJ (hc.sig : E →+* E) J), γ ∈ (SI c).range ↔ bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (Y c).1).toMonoidHom) ∧ lev.Lb = baseLb E n ST ∧ lev.U = (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj b).toMonoidHom ∧ (∀ (x : lev.U) (z : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q), x.1 = b * z.1 * b⁻¹ → lev.chi x = ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ₀)⁻¹ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q →* ℂˣ) z) ∧ (∃ m : ℕ, 0 < m ∧ ∀ κ, lev.chi κ ^ m = 1) ∧ (∀ c, (Y c).1 = y c * b⁻¹) ∧ ∀ c a, (SI c a).1 = st c a := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q K _ Hw π T f hB hTπ hST hcard hSG hidx lam Θ q hO hQT σ₀ b hbU hbV hbL hbT hbO J hJ bad hb
    cl stab _ lat s y hy hd hs hlat st hinj hr hchr
  subst hJ hb
  classical
  let S := stepOfQ hc n Hw q hB hTπ hST hcard hSG hidx lam hO hQT σ₀
  have hbT' : ∀ v, (T : 𝓞 F) ∈ v.asIdeal →
      (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = S.Uloc v := by
    intro v hv
    rw [S.UlocAlt v hv]
    exact hbT v ((mem_plUnder_iff_norm hc hST T hTπ v).2 hv)
  obtain ⟨S', hLb, hU, hchi⟩ := GlobalTheory.T.exists_stepLevel_conj_baseLatticeUnitary S b hbU hbV hbT' hbO
  have hlam : ∃ m : ℕ, 0 < m ∧ ∀ h, lam h ^ m = 1 := by
    haveI : Finite (GLG E n SG) := inferInstance
    refine ⟨Nat.card (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)), Nat.card_pos, fun h => ?_⟩
    rw [← map_pow, pow_card_eq_one', map_one]
  obtain ⟨m, hm, hM⟩ := stepOfQ_chi_fin hc n Hw q hB hTπ hST hcard hSG hidx lam hO hQT σ₀ hlam hchr
  let e := Equiv.ofBijective _ hs
  let s' : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ → DecoF E n ST SG Q := fun c => s (e.symm c)
  have hs' : ∀ c, (Quotient.mk'' (s' c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ) = c :=
    fun c => e.apply_symm_apply c
  let y' : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ → UAd hc n := fun c => ⟨y (e.symm c), hy _⟩
  have hy' : ∀ c, FrOver q (y' c).1 (s' c) := fun c => hd _
  let C := recClsFy q (qdf_frLat q) qdf_frExists s' hs' y' hy'
  have hm' : ∀ c a, st c a ∈ URat hc n := fun c a => by
    obtain ⟨g, hg, -⟩ := (hr c _).1 ⟨a, rfl⟩
    rw [← hg]
    exact ufGL_mem hc n _
  have hYU : ∀ c, y c * b⁻¹ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) :=
    fun c => mul_mem (hy c) (inv_mem hbU)
  refine ⟨S', fun c => ⟨y c * b⁻¹, hYU c⟩, fun c => (st c).codRestrict _ (hm' c), ?_, fun c x => ?_,
    fun c a a' h => hinj c (congrArg Subtype.val h), fun c γ => ?_, hLb, hU, fun x z h => hchi x z h, ?_,
    fun _ => rfl, fun _ _ => rfl⟩
  ·
    have hC : ∀ c, C.y (e c) = ⟨y c, hy c⟩ := fun c => Subtype.ext (congrArg y (e.symm_apply_apply c))
    have hz := C.y_bij.comp e.bijective
    have hz' : Function.Bijective fun c => (Quotient.mk'' (⟨y c, hy c⟩ : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E)
        (FiniteAdeleRing (𝓞 F) F)) : ClassSet ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf
          (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        ((levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))) := by
      convert hz using 2 with c
      simp only [Function.comp_apply, hC]
    exact dc_mul_inv_bij ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf
          (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        ((levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        (S'.U.subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))) ⟨b, hbU⟩ (fun x => by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hU, mem_map_conj]
      rfl) _ hz'
  ·
    have h := decoRaw_carries hc n ST SG (hy c) x
    rw [← rlc_decoOf_val hc n ST SG (hy c), (hd c).1, ← hlat] at h
    refine (h.trans ?_)
    rw [hLb]
    show _ ↔ ((y c * b⁻¹)⁻¹ : GL (Fin n) _).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hbL _).symm
  ·
    have h := C.stabI_range (e c) γ.1 γ.2
    change (⟨γ.1, γ.2⟩ : URat hc n) ∈ (qdStab (hc := hc) (Θ := Θ) (Subgroup.pi Set.univ Hw) (s (e.symm (e c)))).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈
        (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj (y (e.symm (e c)))).toMonoidHom at h
    rw [e.symm_apply_apply, mem_range_qdStab, ← hr] at h
    refine Iff.trans ⟨fun ⟨a, ha⟩ => ⟨a, congrArg Subtype.val ha⟩, fun ⟨a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩ (h.trans ?_)
    rw [hU, mem_map_conj, mem_map_conj, mem_map_conj]
    show _ ↔ b⁻¹ * ((y c * b⁻¹)⁻¹ * _ * (y c * b⁻¹)) * b ∈ _
    have e2 : ∀ g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), b⁻¹ * ((y c * b⁻¹)⁻¹ * g * (y c * b⁻¹)) * b = (y c)⁻¹ * g * y c :=
      fun g => by group
    rw [e2]
    exact Iff.rfl
  ·
    refine ⟨m, hm, fun κ => ?_⟩
    have h1 : ∀ x, x ∈ S'.U → b⁻¹ * x * b ∈ S.U := fun x hx => by
      rw [hU, mem_map_conj] at hx
      exact hx
    have hk : b⁻¹ * κ.1 * b ∈ S.U := h1 κ.1 κ.2
    rw [hchi κ ⟨_, hk⟩ (by show κ.1 = b * (b⁻¹ * κ.1 * b) * b⁻¹; group), hM]

end GlobalTheory.Mem.Col2.ChEx
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugated_chartData_localLevel_at_Q : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) {π : 𝓞 E} {T f : ℕ} (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal) (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG) (hidx : (baseLb E n ST).toAddSubgroup.relIndex (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f)) (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) →* ℂˣ) {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hO : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ) (b : GL (Fin n) (AfE F E)) (hbU : b ∈ UAd hc n) (hbV : ∀ v, bc (prV (E := E) v) b ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) (hbL : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, b.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) (hbT : ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)) (hbO : ∀ v, v ∉ badQ' (F := F) SG Q → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1) (bad : Set (HeightOneSpectrum (𝓞 F))) (hb : bad = badQ' (F := F) SG Q) {cl : Type} (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin n → E)) (s : cl → DecoF E n ST SG Q) (y : cl → GL (Fin n) (AfE F E)) (hy : ∀ c, y c ∈ UAd hc n) (hd : ∀ c, FrOver q (y c) (s c)) (hs : Function.Bijective fun c => (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ)) (hlat : ∀ c, lat c = (s c).deco.1.L) (st : ∀ c, stab c →* GL (Fin n) E) (hinj : ∀ c, Function.Injective (st c)) (hr : ∀ c γ, γ ∈ (st c).range ↔ ∃ g : UF E n × ↥(Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) × ↥Θ.grp, ufGL E n g.1 = γ ∧ g • s c = s c) (hchr : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ k, q.chr P k ^ m = 1), ∃ (lev : StepLevel F E hc.sig J T f bad) (Y : cl → UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (SI : ∀ c, stab c →* UJ (hc.sig : E →+* E) J), Function.Bijective (fun c => (Quotient.mk'' (Y c) : Cls lev)) ∧ (∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F), x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔ ((Y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb) ∧ (∀ c, Function.Injective (SI c)) ∧ (∀ c (γ : UJ (hc.sig : E →+* E) J), γ ∈ (SI c).range ↔ bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (Y c).1).toMonoidHom) ∧ lev.Lb = baseLb E n ST ∧ lev.U = (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj b).toMonoidHom ∧ (∀ (x : lev.U) (z : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q), x.1 = b * z.1 * b⁻¹ → lev.chi x = ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ₀)⁻¹ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q →* ℂˣ) z) ∧ (∃ m : ℕ, 0 < m ∧ ∀ κ, lev.chi κ ^ m = 1) ∧ (∀ c, (Y c).1 = y c * b⁻¹) ∧ ∀ c a, (SI c a).1 = st c a := by
  atlas_forward_decl GlobalTheory.Mem.Col2.ChEx.chartQ_exists
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem frExact_of_isPtOf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ), (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → ∀ {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}, IsPtOf hc g p → g ∈ UAd hc n ∧ FrExact q g p := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q K _ Θ q hQ g p hp
  have h1 : IsPtOf hc (g * 1) p := by rwa [mul_one]
  have hres : ∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 (((1 : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 r j))
      (if j = r then (((1 : DiaG E ST) P : (𝓞 E ⧸ P.1.asIdeal)ˣ) : 𝓞 E ⧸ P.1.asIdeal) else 0) := by
    intro P r j _
    rw [inv_one, Units.val_one]
    by_cases h : j = r
    · subst h
      rw [Matrix.one_apply_eq, map_one, if_pos rfl]
      simpa using hasRes_coe P.1 1
    · rw [Matrix.one_apply_ne (Ne.symm h), map_zero, if_neg h]
      simpa using hasRes_coe P.1 0
  obtain ⟨hU, hd⟩ := GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul F E hc n ST SG Q g 1 p 1 h1 ⟨DecoF.base E n ∅ ∅ ∅, isPtOf_base hc, rfl⟩
    (fun w _ => map_one _) hres
  rw [DecoSet.dia_one] at hd
  refine ⟨hU, hd, fun P => Units.ext (Matrix.ext fun i j => ?_)⟩
  rw [qdf_at_val]
  show qPi q P ((g : Matrix (Fin n) (Fin n) _) i j) = q.phi P (((qGL n (p.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [qsp_toGLm_apply]
  exact GlobalTheory.T.splitLocalLevel_firstFactor_reads_component hc n q P (hQ P) _ _ (hp.fr P i j)

end GlobalTheory.Mem.Col2.ChEx
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framesExact_of_isAdelicPointOfFramedLattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ), (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → ∀ {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}, IsPtOf hc g p → g ∈ UAd hc n ∧ FrExact q g p := by
  atlas_forward_decl GlobalTheory.Mem.Col2.ChEx.frExact_of_isPtOf
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem frStab_iff_image {P : HeightOneSpectrum (𝓞 E)} {C : Set (Sp E n)} (g : ↥(GLint E n P)) :
    g ∈ frStab P C ↔ (fun v => g.1 v) '' C = C := by
  constructor
  · intro h
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).2 hw
    · intro hv
      have e : g.1 ((g⁻¹).1 v) = v := LinearEquiv.apply_symm_apply g.1 v
      refine ⟨(g⁻¹).1 v, ?_, e⟩
      have h' := h ((g⁻¹).1 v)
      rw [e] at h'
      exact h'.1 hv
  · intro h v
    constructor
    · intro hv
      rw [← h] at hv
      obtain ⟨w, hw, e⟩ := hv
      rwa [← g.1.injective e]
    · intro hv
      rw [← h]
      exact ⟨v, hv, rfl⟩

end SlopeTestRemainingChoices

theorem lev_iff_frames : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)), GlobalTheory.Mem.Col2.ChEx.InvActs cq → ∀ (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)), bar r = C → ∀ (D : ∀ P : Q, Set (Sp X.E n)), cq r = D → ∀ (q : QLoc hc n Q (GlobalTheory.Mem.Col2.ChEx.cutQ Θ D)) {g s : GL (Fin n) (AfE X.F X.E)}, g ∈ UAd hc n → g * s ∈ UAd hc n → ∀ (p : DecoF X.E n ST SG Q), FrExact q g r.1.1 → FrExact q (g * s) p → (s ∈ levUQ hc n ST SG Q (chG Λ C) q ↔ ∃ κ : FrmG Λ Θ, ufGL X.E n κ.1 = 1 ∧ (ya Λ Θ κ r).1.1 = p ∧ bar (ya Λ Θ κ r) = bar r ∧ cq (ya Λ Θ κ r) = cq r) := by
  intro X n ST SG Q y _ hc cq hact Λ Θ r C hC D hD q g s hg hgs p hr hp
  have hmul : ∀ P : Q, q.at P (g * s) = q.at P g * q.at P s := fun P => by simp only [QLoc.at, map_mul]
  have hat : ∀ P : Q, bc (q.phi P) (qGL n (r.1.1.fr P)) * q.at P s = bc (q.phi P) (qGL n (p.fr P)) := fun P => by
    rw [← hr.2 P, ← hp.2 P, hmul]
  have hcq : ∀ κ : FrmG Λ Θ, (∀ P : Q, κ.2.2.1 P ∈ frStab P.1 (D P)) ↔ cq (ya Λ Θ κ r) = cq r := by
    intro κ
    rw [funext_iff]
    refine forall_congr' fun P => ?_
    rw [hact Λ Θ κ r P, hD, frStab_iff_image]
  constructor
  · intro hs
    obtain ⟨hsU, hsQ⟩ := (mem_levUQ q _).1 hs
    have h1 := act_of_mem hc n _ 1 hg ⟨s, hsU⟩
    rw [DecoSet.dia_one, DecoSet.dia_one, hr.1, hp.1] at h1
    have h2 := mem_chG.1 ((Formalism.L2.Col.levRed hc n ST SG _ ⟨s, hsU⟩)⁻¹).2
    have hN : ∀ (P : Q) (x : Sp X.E n), x ∈ p.deco.1.at P.1 ↔ x ∈ r.1.1.deco.1.at P.1 := by
      intro P x
      rw [h1]
      exact (mem_localization_gmap P.1 ((1 : UF X.E n) : Sp X.E n ≃ₗ[X.E] Sp X.E n) r.1.1.deco.1.N x).trans Iff.rfl
    let t : GLQ X.E n Q := fun P => ⟨(r.1.1.fr P)⁻¹ * p.fr P, by
      show ∀ x, _ ↔ _
      intro x
      have A := r.1.1.2 P (((r.1.1.fr P)⁻¹ * p.fr P) x)
      have e : r.1.1.1.2 P (((r.1.1.fr P)⁻¹ * p.fr P) x) = p.fr P x := LinearEquiv.apply_symm_apply _ _
      rw [e] at A
      exact A.symm.trans ((hN P _).symm.trans (p.2 P x))⟩
    have hs_at : ∀ P : Q, q.at P s = bc (q.phi P) (qGL n (t P).1) := fun P => by
      rw [eq_inv_mul_of_mul_eq (hat P)]
      show _ = bc (q.phi P) (qGL n ((r.1.1.fr P)⁻¹ * p.fr P))
      simp only [qGL, map_mul, map_inv]
    have ht : ∀ P : Q, t P ∈ (cutQ Θ D P).H := fun P => by
      refine (q.U_rat P (t P)).1 ?_
      have h' := hsQ P
      rw [hs_at P] at h'
      exact h'
    have hθ : (fun P => (t P)⁻¹ : GLQ X.E n Q) ∈ Θ.grp := fun P _ => inv_mem (Subgroup.mem_inf.1 (ht P)).1
    let κ : FrmG Λ Θ := (1, ⟨_, h2.1⟩, ⟨_, hθ⟩)
    refine ⟨κ, map_one _, ?_, (bar_ya_eq_iff _ _ _ _).2 ?_, (hcq κ).1 fun P => inv_mem (Subgroup.mem_inf.1 (ht P)).2⟩
    · apply Subtype.ext
      apply Prod.ext
      · exact h1.symm
      · funext P
        show 1 * r.1.1.1.2 P * (((t P)⁻¹)⁻¹).1 = p.1.2 P
        rw [inv_inv, one_mul]
        exact mul_inv_cancel_left (r.1.1.fr P) (p.fr P)
    · rw [hC]
      exact h2.2
  · rintro ⟨⟨γ, h, θ⟩, h1, h2, h3, h4⟩
    have : γ = 1 := ufGL_inj hc n (h1.trans (map_one _).symm)
    subst this
    have hdeco : p.deco = ((1 : UF X.E n), h.1) • r.1.1.deco := by
      rw [← h2]
      rfl
    obtain ⟨hJ, hred⟩ := red_of_act hc n 1 hg hgs h.1 (by rw [DecoSet.dia_one, DecoSet.dia_one, hr.1, hp.1, hdeco])
    have hsU : s ∈ levU hc n ST SG (chG Λ C) := (mem_levU hc n ST SG _).2 ⟨hJ, by
      rw [hred]
      refine inv_mem (mem_chG.2 ⟨h.2, ?_⟩)
      rw [← hC]
      exact (bar_ya_eq_iff _ _ _ _).1 h3⟩
    refine (mem_levUQ q _).2 ⟨hsU, fun P => ?_⟩
    have hfr : p.fr P = r.1.1.fr P * ((θ.1 P)⁻¹).1 := by
      rw [← h2]
      show 1 * r.1.1.1.2 P * ((θ.1 P)⁻¹).1 = _
      rw [one_mul]
      rfl
    have hs_at : q.at P s = bc (q.phi P) (qGL n ((θ.1 P)⁻¹).1) := by
      rw [eq_inv_mul_of_mul_eq (hat P), hfr]
      simp only [qGL, map_mul, map_inv, inv_mul_cancel_left]
    rw [hs_at]
    refine (q.U_rat P ((θ.1 P)⁻¹)).2 ?_
    exact inv_mem (Subgroup.mem_inf.2 ⟨θ.2 P trivial, (hcq (1, h, θ)).2 h4 P⟩)

end GlobalTheory.Mem.Col2.ChEx
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevel_iff_frames_onPoints : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)), GlobalTheory.Mem.Col2.ChEx.InvActs cq → ∀ (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)), bar r = C → ∀ (D : ∀ P : Q, Set (Sp X.E n)), cq r = D → ∀ (q : QLoc hc n Q (GlobalTheory.Mem.Col2.ChEx.cutQ Θ D)) {g s : GL (Fin n) (AfE X.F X.E)}, g ∈ UAd hc n → g * s ∈ UAd hc n → ∀ (p : DecoF X.E n ST SG Q), FrExact q g r.1.1 → FrExact q (g * s) p → (s ∈ levUQ hc n ST SG Q (chG Λ C) q ↔ ∃ κ : FrmG Λ Θ, ufGL X.E n κ.1 = 1 ∧ (ya Λ Θ κ r).1.1 = p ∧ bar (ya Λ Θ κ r) = bar r ∧ cq (ya Λ Θ κ r) = cq r) := by
  atlas_forward_decl GlobalTheory.Mem.Col2.ChEx.lev_iff_frames
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

theorem chr_frames : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E) (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (D : ∀ P : Q, Set (Sp X.E n)) (q : QLoc hc n Q (GlobalTheory.Mem.Col2.ChEx.cutQ Θ D)) {g : GL (Fin n) (AfE X.F X.E)} (z : levUQ hc n ST SG Q (chG Λ C) q), g ∈ UAd hc n → ∀ (κ : FrmG Λ Θ), ufGL X.E n κ.1 = 1 → FrExact q g r.1.1 → FrExact q (g * z.1) (ya Λ Θ κ r).1.1 → ((((levTyp (chLam σ Λ C)).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ)⁻¹ : levUQ hc n ST SG Q (chG Λ C) q →* ℂˣ) z : ℂˣ) : ℂ) = σ ((Λ.chr κ.2.1 * Θ.chr κ.2.2 : X.Kˣ) : X.K) := by
  intro X n ST SG Q y _ hc σ Λ Θ r C D q g z hg κ h1 hE hE'
  obtain ⟨γ, h, θ⟩ := κ
  have hγ : γ = 1 := ufGL_inj hc n (h1.trans (map_one _).symm)
  subst hγ

  have hzU : z.1 ∈ levU hc n ST SG (chG Λ C) := levUQ_le q _ z.2
  have hx : g * z.1 ∈ UAd hc n := mul_mem hg (levU_le_UAd hc n ST SG _ hzU)
  have hdeco : decoOf ST SG (g * z.1) = ((1, h.1) : UF X.E n × GLG X.E n SG) • decoOf ST SG g := by
    rw [hE'.1, hE.1]
    rfl
  have e2 : decoRaw ST SG (g * z.1) = (decoRaw ST SG g).act 1 h.1 := by
    rw [← rlc_decoOf_val hc n ST SG hx, ← rlc_decoOf_val hc n ST SG hg, hdeco]
    rfl
  obtain ⟨hJ, hr⟩ := mem_congruence_of_action hc ST SG hx hg h.1 e2
  have e3 : z.1 = ((g * z.1)⁻¹ * g)⁻¹ := by group
  have hJ' : z.1 ∈ J0 hc n ST := e3 ▸ inv_mem hJ
  have hr' : redG hc n ST SG ⟨z.1, hJ'⟩ = h.1⁻¹ := by
    rw [← hr, ← map_inv]
    exact congrArg _ (Subtype.ext e3)
  have hA : levTyp (chLam σ Λ C) (Subgroup.inclusion (levUQ_le q _) z) = (Units.map σ.toMonoidHom (Λ.chr h)) := by
    have h2 : Subgroup.inclusion (chG_le Λ C) (Formalism.L2.Col.levRed hc n ST SG _ (Subgroup.inclusion (levUQ_le q _) z)) = h⁻¹ :=
      Subtype.ext hr'
    show (Units.map σ.toMonoidHom (Λ.chr (Subgroup.inclusion (chG_le Λ C) (Formalism.L2.Col.levRed hc n ST SG _ (Subgroup.inclusion (levUQ_le q _) z)))))⁻¹ = _
    rw [h2, map_inv, map_inv, inv_inv]

  have hP : ∀ P : Q, q.at P z.1 = Formalism.UG.bc (q.phi P) (qGL n ((θ.1 P)⁻¹).1) := fun P => by
    have a1 := hE.2 P
    have a2 := hE'.2 P
    have efr : (ya Λ Θ ((1 : UF X.E n), h, θ) r).1.1.fr P = r.1.1.fr P * ((θ.1 P)⁻¹).1 := by
      show (1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) * r.1.1.fr P * ((θ.1 P)⁻¹).1 = _
      rw [one_mul]
    have a3 : q.at P (g * z.1) = q.at P g * q.at P z.1 := by
      simp only [QLoc.at, map_mul]
    rw [a3, a1, efr] at a2
    simp only [qGL, map_mul] at a2
    exact mul_left_cancel a2
  have hB : ∀ P : Q, q.chr P (lqRes q (chG Λ C) P z) = ((Θ P).lam ⟨θ.1 P, θ.2 P trivial⟩)⁻¹ := fun P => by
    have hmem : Formalism.UG.bc (q.phi P) (qGL n ((θ.1 P)⁻¹).1) ∈ q.U P := hP P ▸ (lqRes q (chG Λ C) P z).2
    have hcut : (θ.1 P)⁻¹ ∈ (cutQ Θ D P).H := (q.U_rat P _).1 hmem
    have e4 : lqRes q (chG Λ C) P z = ⟨_, hmem⟩ := Subtype.ext (hP P)
    rw [e4, q.chr_rat P _ hcut hmem, ← map_inv]
    rfl
  have hT : Θ.chr θ = ∏ P : Q, (Θ P).lam ⟨θ.1 P, θ.2 P trivial⟩ := by
    unfold LevQFam.chr piChar
    erw [MonoidHom.finsetProd_apply]
    rfl
  have hC : chiQ q (chG Λ C) σ z = (Units.map σ.toMonoidHom (Θ.chr θ))⁻¹ := by
    unfold chiQ
    rw [MonoidHom.finsetProd_apply, hT, map_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hB P, map_inv]
  show ((levTyp (chLam σ Λ C) (Subgroup.inclusion (levUQ_le q _) z) * (chiQ q (chG Λ C) σ z)⁻¹ : ℂˣ) : ℂ) = _
  rw [hA, hC, inv_inv, ← map_mul]
  rfl

end GlobalTheory.Mem.Col2.ChEx
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartCharacter_frames_onPoints : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E) (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (D : ∀ P : Q, Set (Sp X.E n)) (q : QLoc hc n Q (GlobalTheory.Mem.Col2.ChEx.cutQ Θ D)) {g : GL (Fin n) (AfE X.F X.E)} (z : levUQ hc n ST SG Q (chG Λ C) q), g ∈ UAd hc n → ∀ (κ : FrmG Λ Θ), ufGL X.E n κ.1 = 1 → FrExact q g r.1.1 → FrExact q (g * z.1) (ya Λ Θ κ r).1.1 → ((((levTyp (chLam σ Λ C)).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ)⁻¹ : levUQ hc n ST SG Q (chG Λ C) q →* ℂˣ) z : ℂˣ) : ℂ) = σ ((Λ.chr κ.2.1 * Θ.chr κ.2.2 : X.Kˣ) : X.K) := by
  atlas_forward_decl GlobalTheory.Mem.Col2.ChEx.chr_frames
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section OrbF

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

theorem image_eq_iff_frStab {P : HeightOneSpectrum (𝓞 X.E)} (C : Set (Sp X.E n)) (g : ↥(GLint X.E n P)) :
    (fun v => g.1 v) '' C = C ↔ g ∈ frStab P C := by
  rw [mem_frStab]
  constructor
  · intro e v
    constructor
    · intro hv
      rw [← e] at hv
      obtain ⟨u, hu, huv⟩ := hv
      rwa [← g.1.injective huv]
    · intro hv
      rw [← e]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (h u).2 hu
    · intro hv
      refine ⟨g.1.symm v, (h _).1 ?_, LinearEquiv.apply_symm_apply g.1 v⟩
      rw [LinearEquiv.apply_symm_apply]
      exact hv

def frLift (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal))
    (D : ∀ P : Q, Set (Sp X.E n)) (g : UF X.E n × chG Λ C × (cutQ Θ D).grp) : FrmG Λ Θ :=
  (g.1, ⟨g.2.1.1, chG_le _ _ g.2.1.2⟩, ⟨g.2.2.1, cutQ_grp_le _ _ g.2.2.2⟩)

theorem ya_frLift (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal))
    (D : ∀ P : Q, Set (Sp X.E n)) (g : UF X.E n × chG Λ C × (cutQ Θ D).grp) (q : PtY ST SG Q y) :
    (ya Λ Θ (frLift Λ Θ C D g) q).1.1 = g • q.1.1 := rfl

end OrbF

end GlobalTheory.Mem.Col2.ChEx

namespace GlobalTheory.Mem.Col2.ChEx

theorem clsF_bij : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) [NeZero n], GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → (∀ (r : PtY ST SG Q y) (p : DecoF X.E n ST SG Q), ∃ r' : PtY ST SG Q y, r'.1.1 = p ∧ bar r' = bar r ∧ cq r' = cq r) → (∀ b r r', bar r = bar r' → cq r = cq r' → bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')) ∧ cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r'))) → ∀ (c₀ : (stR Λ Θ p₀ pref).Cl) (p : (stR Λ Θ p₀ pref).Cl → Prop), (∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rp Λ Θ p₀ pref c) = bar (rp Λ Θ p₀ pref c₀) ∧ cq (rp Λ Θ p₀ pref c) = cq (rp Λ Θ p₀ pref c₀)) → Function.Bijective fun c : {c // p c} => (Quotient.mk'' (rp Λ Θ p₀ pref c.1).1.1 : DecoFCl (K := X.K) n ST SG Q (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀))) (GlobalTheory.Mem.Col2.ChEx.cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀)))) := by
  intro X n ST SG Q y β _ _ Λ Θ p₀ pref cq _ hact hdet hsur hnorm c₀ p hp
  constructor
  · rintro ⟨c, h⟩ ⟨c', h'⟩ e
    obtain ⟨h1, h2, h3⟩ := (hp c).1 h
    obtain ⟨h1', h2', h3'⟩ := (hp c').1 h'
    apply Subtype.ext
    show c = c'
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1 (Quotient.exact' e)
    have hb : bar (ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')) = bar (rp Λ Θ p₀ pref c') :=
      (bar_ya_eq_iff _ _ _ _).2 fun w => by rw [h2']; exact (mem_chG.1 g.2.1.2).2 w
    have hq : cq (ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')) = cq (rp Λ Θ p₀ pref c') := by
      funext P
      rw [hact, h3']
      exact (image_eq_iff_frStab _ _).2 ((mem_cutQ_grp.1 g.2.2.2).2 P)
    have e2 : ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c') = rp Λ Θ p₀ pref c :=
      hdet _ _ (by rw [ya_frLift]; exact hg) (hb.trans (h2'.trans h2.symm)) (hq.trans (h3'.trans h3.symm))
    have e3 := cl_ya Λ Θ p₀ pref c₀.1 (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')
    rw [e2] at e3
    have e4 := cl_rp Λ Θ p₀ pref c
    have e5 := cl_rp Λ Θ p₀ pref c'
    have t : ∀ b b' : β, b = b' → ∀ q : PtY ST SG Q y, (stR Λ Θ p₀ pref).cl b q = (stR Λ Θ p₀ pref).cl b' q := by
      rintro b _ rfl q
      rfl
    exact e4.symm.trans ((t _ _ h1 _).trans (e3.trans ((t _ _ h1' _).symm.trans e5)))
  · intro z
    induction z using Quotient.inductionOn' with
    | h d =>
      obtain ⟨r', h1, h2, h3⟩ := hsur (rp Λ Θ p₀ pref c₀) d
      obtain ⟨hb, hq⟩ := hnorm c₀.1 _ _ h2.symm h3.symm
      rw [cl_rp] at hb hq
      refine ⟨⟨(stR Λ Θ p₀ pref).cl c₀.1 r', (hp _).2 ⟨rfl, hb.symm, hq.symm⟩⟩, ?_⟩
      obtain ⟨g, hg⟩ := exists_ya Λ Θ p₀ pref c₀.1 r'
      rw [hg] at hb hq
      have hb' : bar (ya (Λ c₀.1) (Θ c₀.1) g r') = bar r' := hb.symm.trans h2.symm
      have hq' : cq (ya (Λ c₀.1) (Θ c₀.1) g r') = cq r' := hq.symm.trans h3.symm
      rw [bar_ya_eq_iff, h2] at hb'
      have hC : ∀ P : Q, g.2.2.1 P ∈ frStab P.1 (cq (rp Λ Θ p₀ pref c₀) P) := fun P => by
        rw [← h3, ← image_eq_iff_frStab]
        have := congrFun hq' P
        rwa [hact] at this
      let g' : UF X.E n × chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀)) × (cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀))).grp :=
        (g.1, ⟨g.2.1.1, mem_chG.2 ⟨g.2.1.2, hb'⟩⟩, ⟨g.2.2.1, mem_cutQ_grp.2 ⟨g.2.2.2, hC⟩⟩)
      refine Quotient.sound' (MulAction.orbitRel_apply.2 ⟨g', ?_⟩)
      show g' • d = (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl c₀.1 r')).1.1
      rw [hg, ← h1]
      rfl

end GlobalTheory.Mem.Col2.ChEx
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartClasses_bijective_orbits_framedLattices : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) [NeZero n], GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → (∀ (r : PtY ST SG Q y) (p : DecoF X.E n ST SG Q), ∃ r' : PtY ST SG Q y, r'.1.1 = p ∧ bar r' = bar r ∧ cq r' = cq r) → (∀ b r r', bar r = bar r' → cq r = cq r' → bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')) ∧ cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r'))) → ∀ (c₀ : (stR Λ Θ p₀ pref).Cl) (p : (stR Λ Θ p₀ pref).Cl → Prop), (∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rp Λ Θ p₀ pref c) = bar (rp Λ Θ p₀ pref c₀) ∧ cq (rp Λ Θ p₀ pref c) = cq (rp Λ Θ p₀ pref c₀)) → Function.Bijective fun c : {c // p c} => (Quotient.mk'' (rp Λ Θ p₀ pref c.1).1.1 : DecoFCl (K := X.K) n ST SG Q (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀))) (GlobalTheory.Mem.Col2.ChEx.cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀)))) := by
  atlas_forward_decl GlobalTheory.Mem.Col2.ChEx.clsF_bij
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Mem.Col2.ChEx.stM_range_tw : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)), GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → ∀ (c : (stR Λ Θ p₀ pref).Cl) (b : β), c.1 = b → ∀ (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)), bar (rp Λ Θ p₀ pref c) = C → ∀ (D : ∀ P : Q, Set (Sp X.E n)), cq (rp Λ Θ p₀ pref c) = D → ∀ (γ : GL (Fin n) X.E), (γ ∈ (stM Λ Θ p₀ pref c).range ↔ ∃ g : UF X.E n × ↥(chG (Λ b) C) × ↥(GlobalTheory.Mem.Col2.ChEx.cutQ (Θ b) D).grp, ufGL X.E n g.1 = γ ∧ g • (rp Λ Θ p₀ pref c).1.1 = (rp Λ Θ p₀ pref c).1.1) := by
  intro X n ST SG Q y β _ _ Λ Θ p₀ pref cq hI hD c b hb C hC D hD2 γ
  have img : ∀ (θ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (C : Set (Sp X.E n)), (fun v => θ v) '' C = C ↔ ∀ v, θ v ∈ C ↔ v ∈ C := by
    intro θ C
    constructor
    · intro h v
      constructor
      · intro hv
        rw [← h] at hv
        obtain ⟨w, hw, e⟩ := hv
        rwa [← θ.injective e]
      · intro hv
        rw [← h]
        exact ⟨v, hv, rfl⟩
    · intro h
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (h w).2 hw
      · intro hv
        refine ⟨θ.symm v, (h _).1 ?_, θ.apply_symm_apply v⟩
        rwa [θ.apply_symm_apply]
  subst hb hC hD2
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    replace hg : ya (Λ c.1) (Θ c.1) g (rp Λ Θ p₀ pref c) = rp Λ Θ p₀ pref c := hg
    have hq : ∀ P, g.2.2.1 P ∈ GlobalTheory.Mem.Col2.ChEx.frStab P.1 (cq (rp Λ Θ p₀ pref c) P) := fun P => by
      have h := hI (Λ c.1) (Θ c.1) g (rp Λ Θ p₀ pref c) P
      rw [hg] at h
      exact GlobalTheory.Mem.Col2.ChEx.mem_frStab.2 ((img _ _).1 h.symm)
    refine ⟨(g.1, ⟨g.2.1.1, mem_chG.2 ⟨g.2.1.2, (bar_ya_eq_iff _ _ _ _).1 (congrArg bar hg)⟩⟩,
      ⟨g.2.2.1, GlobalTheory.Mem.Col2.ChEx.mem_cutQ_grp.2 ⟨g.2.2.2, hq⟩⟩), rfl, ?_⟩
    exact congrArg (fun q : PtY ST SG Q y => q.1.1) hg
  · rintro ⟨g, rfl, hg⟩
    have hq := (GlobalTheory.Mem.Col2.ChEx.mem_cutQ_grp.1 g.2.2.2).2
    refine ⟨⟨(g.1, ⟨g.2.1.1, chG_le _ _ g.2.1.2⟩, ⟨g.2.2.1, GlobalTheory.Mem.Col2.ChEx.cutQ_grp_le _ _ g.2.2.2⟩), ?_⟩, rfl⟩
    show ya (Λ c.1) (Θ c.1) _ (rp Λ Θ p₀ pref c) = rp Λ Θ p₀ pref c
    refine hD _ _ hg ((bar_ya_eq_iff _ _ _ _).2 (mem_chG.1 g.2.1.2).2) ?_
    funext P
    rw [hI]
    exact (img _ _).2 (GlobalTheory.Mem.Col2.ChEx.mem_frStab.1 (hq P))
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartClassStabiliser_rationalParts : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)), GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → ∀ (c : (stR Λ Θ p₀ pref).Cl) (b : β), c.1 = b → ∀ (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)), bar (rp Λ Θ p₀ pref c) = C → ∀ (D : ∀ P : Q, Set (Sp X.E n)), cq (rp Λ Θ p₀ pref c) = D → ∀ (γ : GL (Fin n) X.E), (γ ∈ (stM Λ Θ p₀ pref c).range ↔ ∃ g : UF X.E n × ↥(chG (Λ b) C) × ↥(GlobalTheory.Mem.Col2.ChEx.cutQ (Θ b) D).grp, ufGL X.E n g.1 = γ ∧ g • (rp Λ Θ p₀ pref c).1.1 = (rp Λ Θ p₀ pref c).1.1) := by
  atlas_forward_decl GlobalTheory.Mem.Col2.ChEx.stM_range_tw
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_moves_with_frameChange : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → GlobalTheory.Mem.Col2.ChEx.InvActs (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.invActs_cqOf | exact GlobalTheory.Mem.Col2.ChEx.invActs_cqOf | (intros; apply GlobalTheory.Mem.Col2.ChEx.invActs_cqOf <;> assumption)
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

open Classical in

theorem ptDet_cqOf : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ},
    (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) →
    GlobalTheory.Mem.Col2.ChEx.PtDet (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  intro X Pr R sel S mu cst u j hQ hq r r' hfr hb hc
  suffices h2 : r.1.2 = r'.1.2 from Subtype.ext (Prod.ext hfr h2)
  have hd : r.1.1.deco = r'.1.1.deco := congrArg DecoF.deco hfr
  by_cases hj : j + 1 = R.m
  · obtain ⟨y, hy, eY⟩ := (show PtAt R sel mu cst u j from r).mem_ybSet hj
    obtain ⟨y', hy', eY'⟩ := (show PtAt R sel mu cst u j from r').mem_ybSet hj
    have eN : r'.1.1.deco.1.N = r.1.1.deco.1.N := by rw [hd]
    rw [eN] at hy' eY'
    have hyin : y ∈ r.1.2 := by rw [eY, mem_coset, sub_self]; exact zero_mem _
    rw [eY, eY']
    apply coset_eq
    refine (mem_locLat _ _ _ _).2 fun P => ?_
    by_cases hG : P.1 ∈ Pr.vGs
    · rw [if_pos hG, zpow_zero, inv_one, one_smul]
      have hm : r.1.1.deco.1.be ⟨P.1, hG⟩ (((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) • y) ∈ bar r ⟨P.1, hG⟩ := ⟨y, hyin, rfl⟩
      rw [hb] at hm
      obtain ⟨z, hz, ez⟩ := hm
      rw [← hd] at ez
      rw [eY'] at hz
      have hz' := (mem_locLat _ _ _ _).1 (mem_coset.1 hz) P
      rw [if_pos hG, zpow_zero, inv_one, one_smul] at hz'
      have h1 := (mem_locLat _ _ _ _).1 hy P
      have h2 := (mem_locLat _ _ _ _).1 hy' P
      rw [if_pos hG, _root_.zpow_neg_one, inv_inv] at h1 h2
      exact sub_mem_of_be_eq r.1.1.deco.2 ⟨P.1, hG⟩ (hq _ hG) h1 h2 hz' ez
    · rw [if_neg hG, zpow_natCast]
      have hPQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp P.2).resolve_left hG
      have hfrP : frsF sel mu r.1.1 P = r.1.1.fr ⟨P.1, hPQ⟩ := by
        unfold frsF
        rw [dif_neg hG]
      have hc1 : (r.1.1.fr ⟨P.1, hPQ⟩).symm y ∈ cqOf r ⟨P.1, hPQ⟩ := ⟨y, hyin, by
        show ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (_ - (frsF sel mu r.1.1 P).symm y) ∈ _
        rw [hfrP, sub_self, smul_zero]
        exact zero_mem _⟩
      rw [hc] at hc1
      obtain ⟨y0, hy0, hmem⟩ := hc1
      change ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (_ - (frsF sel mu r'.1.1 P).symm y0) ∈ _ at hmem
      rw [if_neg hG, ← hfr, hfrP] at hmem
      have hA := (r.1.1.2 ⟨P.1, hPQ⟩ _).2 hmem
      change r.1.1.fr ⟨P.1, hPQ⟩ _ ∈ _ at hA
      rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hA
      rw [eY'] at hy0
      have hB := (mem_locLat _ _ _ _).1 (mem_coset.1 hy0) P
      rw [if_neg hG, zpow_natCast] at hB
      have := add_mem hA hB
      rwa [← smul_add, sub_add_sub_cancel] at this
  · have h1 := r.2
    have h1' := r'.2
    rw [ysAt_ys_of_ne sel mu cst hj] at h1 h1'
    exact h1.trans h1'.symm

end GlobalTheory.Mem.Col2.ChEx
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepPoint_determined_by_latticeInvariants : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → GlobalTheory.Mem.Col2.ChEx.PtDet (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  atlas_forward_decl GlobalTheory.Mem.Col2.ChEx.ptDet_cqOf
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCosetsInFrames_eq_iff_reductions : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ (r r' : PtAt R sel mu cst u j), cosetIn r = cosetIn r' ↔ bar r = bar r' ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r = GlobalTheory.Mem.Col2.ChEx.cqOf r' := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.cosetIn_eq_iff_bar_cq | exact GlobalTheory.Mem.Col2.ChEx.cosetIn_eq_iff_bar_cq | (intros; apply GlobalTheory.Mem.Col2.ChEx.cosetIn_eq_iff_bar_cq <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem cqOf_empty_or_coset : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)), GlobalTheory.Mem.Col2.ChEx.cqOf r P = ∅ ∨ ∃ (z : Sp X.E (R.N j)) (c : X.E), c ≠ 0 ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r P = {x | c⁻¹ • (x - z) ∈ stdAt X.E (R.N j) P.1} := by
  intro X Pr R sel S mu cst u j hQ r P
  classical
  have hP : P.1 ∉ Pr.vGs := hQ P.1 P.2
  by_cases hj : j + 1 = R.m
  · right
    obtain ⟨y0, -, hY⟩ := r.mem_ybSet hj
    have hq : ((qOf P.1 : X.E) ^ cst.M) ≠ 0 := pow_ne_zero _ (by
      rw [Nat.cast_ne_zero]
      unfold qOf
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact P.1.ne_bot)
    refine ⟨(frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y0, (qOf P.1 : X.E) ^ cst.M, hq, ?_⟩
    ext x
    simp only [cqOf, cosetIn, Set.mem_setOf_eq, if_neg hP]
    constructor
    · rintro ⟨y, hy, hx⟩
      rw [hY] at hy
      have h1 := (mem_locLat _ _ _ _).1 hy ⟨P.1, Finset.mem_union_right _ P.2⟩
      simp only [if_neg hP, zpow_natCast] at h1
      have h2 := (GlobalTheory.ColPeriod.TopTwist.frsF_mem' sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩ hP
        (((qOf P.1 : X.E) ^ cst.M)⁻¹ • ((frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y -
          (frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y0))).1 (by
        rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact h1)
      have h3 := Submodule.add_mem _ hx h2
      convert h3 using 1
      rw [← smul_add]
      congr 1
      abel
    · intro hx
      exact ⟨y0, by rw [hY]; simp, hx⟩
  · left
    have h1 : r.1.2 = ∅ := by
      have := r.2
      rwa [ysAt_ys_of_ne _ _ _ hj] at this
    ext x
    simp [cqOf, cosetIn, h1]

end GlobalTheory.Mem.Col2.ChEx
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_twistPrime_empty_or_coset : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)), GlobalTheory.Mem.Col2.ChEx.cqOf r P = ∅ ∨ ∃ (z : Sp X.E (R.N j)) (c : X.E), c ≠ 0 ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r P = {x | c⁻¹ • (x - z) ∈ stdAt X.E (R.N j) P.1} := by
  atlas_forward_decl GlobalTheory.Mem.Col2.ChEx.cqOf_empty_or_coset
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

open Classical in
set_option maxHeartbeats 4000000 in

theorem thetaOpen_levQ : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}, L.Ok Ch sel mu cst G m2 → (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (j : ℕ) (b : L.β j), ThetaOpen (L.levQ j b) := by
  intro X Pr R Ch sel S mu cst L G m2 hL hQg j b P
  have hc : cst.Ok := hL.cst_ok
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  let h : AutY X R j := L.h j b P'
  have hPg := hQg P.1 P.2
  have hq := ciQ_mem P.1
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h0
    exact P.1.ne_bot ((Ideal.absNorm_eq_zero_iff).1 h0)
  obtain ⟨a, ha⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨b', hb⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h⁻¹ : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨e, he⟩ := qth_exists_e P.1 hq0
  refine ⟨a + b' + e + 1, by omega, fun g hg => ?_⟩
  let r : AutY X R j := twZrExt (c := cOf R j) g.1
  have hr := qth_ext_close (c := cOf R j) P.1 g.1 _ hg
  have hrinv : r⁻¹ = twZrExt (c := cOf R j) (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 := LinearEquiv.ext fun v => rfl
  have hr' := qth_ext_close (c := cOf R j) P.1 (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 _ (qth_princ_inv P.1 g hg)
  have hy : QClose P.1 (qOf P.1) (h⁻¹ * r * h) := qth_conj_close P.1 (qOf P.1) h r a b' _ e ha hb hr he (by omega)
  have hy' : QClose P.1 (qOf P.1) (h⁻¹ * r * h)⁻¹ := by
    have e3 : (h⁻¹ * r * h)⁻¹ = h⁻¹ * r⁻¹ * h := by simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [e3, hrinv]
    exact qth_conj_close P.1 (qOf P.1) h _ a b' _ e ha hb hr' he (by omega)
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1 := by
    rw [twJat_Q cst.sharp j hPg]
    exact qth_mem_JQ P.1 (qOf P.1) hq0 (R.k + j) _ hy hy'
  have hC : r ∈ Loc.Cbe (Jat (Pr := Pr) (R := R) cst.sharp j P.1) h := by
    refine ⟨zeroExtension_mem_R1 g.1, ?_⟩
    show (MulAut.conj h⁻¹) r ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1
    simpa [MulAut.conj_apply] using hJ
  have hmem : g.1 ∈ prCat (Pr := Pr) cst.sharp j P.1 h := ⟨r, hC, twZrExt_inX g.1⟩
  have hH : g ∈ (L.levQ j b P).H := by
    rw [hL.grpQ j b P]
    exact Subgroup.mem_subgroupOf.2 hmem
  refine ⟨hH, ?_⟩
  apply Units.ext
  rw [hL.chrQ j b P ⟨g, hH⟩ r hC (fun x => twZrExt_inX g.1 x)]
  have hstd : r ∈ stabL X.E (R.N j + cOf R j) (stdAt X.E (R.N j + cOf R j) P.1) :=
    twZrExt_stab P.1 _ (fun v => ciMem_stdAt P.1 v) g.2
  have hint : IntAt P.1 (Loc.n1Arg r) := by
    unfold Loc.n1Arg
    refine ciIntAt_sum _ _ fun i _ => ?_
    have hv : r (Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1)) ∈ stdAt X.E (R.N j + cOf R j) P.1 :=
      (hstd _).2 (twZr_eN_mem P.1 _ _)
    rw [ciMem_stdAt] at hv
    unfold Loc.atN
    split_ifs
    · exact hv _
    · exact ciIntAt_zero
  unfold chiInv
  rw [hc.psi_int P' _ hint, inv_one, one_mul]
  unfold lamRow
  rw [if_neg hPg]
  exact qth_lamQB_one hq hq0 _ _ hy

end GlobalTheory.Mem.Col2.ChEx
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAtTwistPrimes_isOpen : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}, L.Ok Ch sel mu cst G m2 → (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (j : ℕ) (b : L.β j), ThetaOpen (L.levQ j b) := by
  atlas_forward_decl GlobalTheory.Mem.Col2.ChEx.thetaOpen_levQ
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem T_notMem_qv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (B.primes X).Ok → ∀ (u : B.Word) (a : I.ι) (P : I.Q a), (B.T u : 𝓞 B.host.F) ∉ (qv B.host.F P.1).asIdeal := by
  classical
  intro B X I hI _ u a P
  have hP : P.1 ∈ uSG (B.primes X).vGs I.SQ := Finset.mem_union.2 (Or.inr (I.mem_SQ.2 ⟨a, P.2⟩))
  exact GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P.1 hP

end GlobalTheory.Mem.Col2.ChEx
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberLevelPrime_not_under_twistPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (B.primes X).Ok → ∀ (u : B.Word) (a : I.ι) (P : I.Q a), (B.T u : 𝓞 B.host.F) ∉ (qv B.host.F P.1).asIdeal := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.T_notMem_qv | exact GlobalTheory.Mem.Col2.ChEx.T_notMem_qv | (intros; apply GlobalTheory.Mem.Col2.ChEx.T_notMem_qv <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChExM

open GlobalTheory.Mem.Col2.ChEx

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)}

theorem k_facts {π : 𝓞 E} (hB : BasePi ST π) (k : GL (Fin n) (AfE F E)) (c : DiaG E ST)
    (hk : ∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = stdLat E n)
    (hT : ∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j))
      (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) :
    k ∈ UAd hc n ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) ∧
    (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      k.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) ∧
    ∀ v, v ∈ plUnder F ST →
      (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map
        (MulAut.conj (bc (prV (E := E) v) k)).toMonoidHom =
      levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) :=
  GlobalTheory.T.admissibleBasePoint_unitary_normalisesLevel hc n hB k c hk hT

theorem qb_chr_root {K : Type} [Field K] (Θ : LevQFam E K n Q) (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ) (P : Q) :
    ∃ m : ℕ, 0 < m ∧ ∀ k, (qbLoc hc Θ hQ hΘ).chr P k ^ m = 1 :=
  GlobalTheory.T.localLevelCharacter_finiteOrder hc Θ hQ hΘ P

theorem thetaOpen_cutQ {K : Type} [Field K] (Θ : LevQFam E K n Q) (hΘ : ThetaOpen Θ) (C : ∀ P : Q, Set (Sp E n))
    (hC : ∀ P : Q, C P = ∅ ∨ ∃ (z : Sp E n) (c : E), c ≠ 0 ∧ C P = {x | c⁻¹ • (x - z) ∈ stdAt E n P.1}) : ThetaOpen (cutQ Θ C) :=
  GlobalTheory.T.openLevel_cutByCosetStabiliser Θ hΘ C hC

theorem chartQ_exists {K : Type} [Field K] (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) {π : 𝓞 E} {T f : ℕ}
    (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T)
    (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG)
    (hidx : (baseLb E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f))
    (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) →* ℂˣ)
    {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hO : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ)
    (b : GL (Fin n) (AfE F E)) (hbU : b ∈ UAd hc n)
    (hbV : ∀ v, bc (prV (E := E) v) b ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST))
    (hbL : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      b.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST))
    (hbT : ∀ v, v ∈ plUnder F ST →
      (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map
        (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom =
      levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v))
    (hbO : ∀ v, v ∉ badQ' (F := F) SG Q → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1)
    (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1) (bad : Set (HeightOneSpectrum (𝓞 F))) (hb : bad = badQ' (F := F) SG Q)
    {cl : Type} (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin n → E))
    (s : cl → DecoF E n ST SG Q) (y : cl → GL (Fin n) (AfE F E)) (hy : ∀ c, y c ∈ UAd hc n) (hd : ∀ c, FrOver q (y c) (s c))
    (hs : Function.Bijective fun c => (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ))
    (hlat : ∀ c, lat c = (s c).deco.1.L)
    (st : ∀ c, stab c →* GL (Fin n) E) (hinj : ∀ c, Function.Injective (st c))
    (hr : ∀ c γ, γ ∈ (st c).range ↔ ∃ g : UF E n × ↥(Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) × ↥Θ.grp, ufGL E n g.1 = γ ∧ g • s c = s c)
    (hchr : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ k, q.chr P k ^ m = 1) :
    ∃ (lev : StepLevel F E hc.sig J T f bad) (Y : cl → UPts hc.sig J (FiniteAdeleRing (𝓞 F) F))
      (SI : ∀ c, stab c →* UJ (hc.sig : E →+* E) J),
      Function.Bijective (fun c => (Quotient.mk'' (Y c) : Cls lev)) ∧
      (∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
        x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔
        ((Y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb) ∧
      (∀ c, Function.Injective (SI c)) ∧
      (∀ c (γ : UJ (hc.sig : E →+* E) J), γ ∈ (SI c).range ↔
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (Y c).1).toMonoidHom) ∧
      lev.Lb = baseLb E n ST ∧ lev.U = (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj b).toMonoidHom ∧
      (∀ (x : lev.U) (z : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q), x.1 = b * z.1 * b⁻¹ →
        lev.chi x = ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ₀)⁻¹ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q →* ℂˣ) z) ∧
      (∃ m : ℕ, 0 < m ∧ ∀ κ, lev.chi κ ^ m = 1) ∧ (∀ c, (Y c).1 = y c * b⁻¹) ∧ ∀ c a, (SI c a).1 = st c a :=
  GlobalTheory.T.exists_conjugated_chartData_localLevel_at_Q hc n Hw hB hTπ hST hcard hSG hidx lam q hO hQT σ₀ b hbU hbV hbL hbT hbO J hJ bad hb stab lat s y hy hd hs hlat st hinj hr hchr

theorem frExact_of_isPtOf {K : Type} [Field K] {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) : g ∈ UAd hc n ∧ FrExact q g p :=
  GlobalTheory.T.framesExact_of_isAdelicPointOfFramedLattice hc n q hQ h

end Gen

end GlobalTheory.Mem.Col2.ChExM

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChExM

open GlobalTheory.Mem.Col2.ChEx

section Mid

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

variable [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E)

theorem lev_iffQ (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) (hact : InvActs cq) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)
    (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (hC : bar r = C) (D : ∀ P : Q, Set (Sp X.E n)) (hD : cq r = D)
    (q : QLoc hc n Q (cutQ Θ D)) {g s : GL (Fin n) (AfE X.F X.E)} (hg : g ∈ UAd hc n) (hx : g * s ∈ UAd hc n) (p : DecoF X.E n ST SG Q)
    (e : FrExact q g r.1.1) (e' : FrExact q (g * s) p) :
    s ∈ levUQ hc n ST SG Q (chG Λ C) q ↔
      ∃ κ : FrmG Λ Θ, ufGL X.E n κ.1 = 1 ∧ (ya Λ Θ κ r).1.1 = p ∧ bar (ya Λ Θ κ r) = bar r ∧ cq (ya Λ Θ κ r) = cq r :=
  GlobalTheory.T.chartLevel_iff_frames_onPoints hc cq hact Λ Θ r C hC D hD q hg hx p e e'

theorem chr_eqQ (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y)
    (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (D : ∀ P : Q, Set (Sp X.E n)) (q : QLoc hc n Q (cutQ Θ D))
    {g : GL (Fin n) (AfE X.F X.E)} (z : levUQ hc n ST SG Q (chG Λ C) q) (hg : g ∈ UAd hc n) (κ : FrmG Λ Θ) (h1 : ufGL X.E n κ.1 = 1)
    (e : FrExact q g r.1.1) (e' : FrExact q (g * z.1) (ya Λ Θ κ r).1.1) :
    ((((levTyp (chLam σ Λ C)).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ)⁻¹ : levUQ hc n ST SG Q (chG Λ C) q →* ℂˣ) z : ℂˣ) : ℂ) =
      σ ((Λ.chr κ.2.1 * Θ.chr κ.2.2 : X.Kˣ) : X.K) :=
  GlobalTheory.T.chartCharacter_frames_onPoints hc σ Λ Θ r C D q z hg κ h1 e e'

end Mid

section Orb

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β]
  (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop)
  (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n))

theorem cls_bijQ [NeZero n] (hact : InvActs cq) (hinj : PtDet cq)
    (hsur : ∀ (r : PtY ST SG Q y) (p : DecoF X.E n ST SG Q), ∃ r' : PtY ST SG Q y, r'.1.1 = p ∧ bar r' = bar r ∧ cq r' = cq r)
    (hnorm : ∀ b r r', bar r = bar r' → cq r = cq r' →
      bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')) ∧
      cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')))
    (c₀ : (stR Λ Θ p₀ pref).Cl) (p : (stR Λ Θ p₀ pref).Cl → Prop)
    (hp : ∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rp Λ Θ p₀ pref c) = bar (rp Λ Θ p₀ pref c₀) ∧ cq (rp Λ Θ p₀ pref c) = cq (rp Λ Θ p₀ pref c₀)) :
    Function.Bijective fun c : {c // p c} =>
      (Quotient.mk'' (rp Λ Θ p₀ pref c.1).1.1 : DecoFCl (K := X.K) n ST SG Q (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀)))
        (cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀)))) :=
  GlobalTheory.T.chartClasses_bijective_orbits_framedLattices Λ Θ p₀ pref cq hact hinj hsur hnorm c₀ p hp

theorem stM_rangeQ (hact : InvActs cq) (hinj : PtDet cq) (c : (stR Λ Θ p₀ pref).Cl) (b : β) (hb : c.1 = b)
    (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (hC : bar (rp Λ Θ p₀ pref c) = C)
    (D : ∀ P : Q, Set (Sp X.E n)) (hD : cq (rp Λ Θ p₀ pref c) = D) (γ : GL (Fin n) X.E) :
    γ ∈ (stM Λ Θ p₀ pref c).range ↔ ∃ g : UF X.E n × ↥(chG (Λ b) C) × ↥(cutQ (Θ b) D).grp, ufGL X.E n g.1 = γ ∧
      g • (rp Λ Θ p₀ pref c).1.1 = (rp Λ Θ p₀ pref c).1.1 :=
  GlobalTheory.T.chartClassStabiliser_rationalParts Λ Θ p₀ pref cq hact hinj c b hb C hC D hD γ

end Orb

section PtL

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

theorem cqOf_acts (hd : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) :
    InvActs (cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) :=
  GlobalTheory.T.couplingCoset_moves_with_frameChange hd

theorem cqOf_det (hd : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs)
    (hq : ∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) :
    PtDet (cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) :=
  GlobalTheory.T.stepPoint_determined_by_latticeInvariants hd hq

theorem cosetIn_iff (hd : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs)
    (hq : ∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) (r r' : PtAt R sel mu cst u j) :
    cosetIn r = cosetIn r' ↔ bar r = bar r' ∧ cqOf r = cqOf r' :=
  GlobalTheory.T.couplingCosetsInFrames_eq_iff_reductions hd hq r r'

theorem exists_pt_inv (hd : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (r : PtAt R sel mu cst u j)
    (p : ChPt (R := R) sel mu u j) : ∃ r' : PtAt R sel mu cst u j, r'.1.1 = p ∧ bar r' = bar r ∧ cqOf r' = cqOf r :=
  GlobalTheory.T.exists_stepPoint_given_reductions_cosets hd r p

theorem cqOf_form (hd : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)) :
    cqOf r P = ∅ ∨ ∃ (z : Sp X.E (R.N j)) (c : X.E), c ≠ 0 ∧ cqOf r P = {x | c⁻¹ • (x - z) ∈ stdAt X.E (R.N j) P.1} :=
  GlobalTheory.T.couplingCoset_twistPrime_empty_or_coset hd r P

end PtL

section Open

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem thetaOpen_levQ (hL : L.Ok Ch sel mu cst G m2) (hd : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (j : ℕ) (b : L.β j) :
    ThetaOpen (L.levQ j b) :=
  GlobalTheory.T.levelAtTwistPrimes_isOpen hL hd j b

end Open

end GlobalTheory.Mem.Col2.ChExM

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChExM

open GlobalTheory.Mem.Col2.ChEx

section Main

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem trace_not_mem_twistPrime_under (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) : ∀ P : I.Q a, (B.T u : 𝓞 B.host.F) ∉ (qv B.host.F P.1).asIdeal :=
  GlobalTheory.T.memberLevelPrime_not_under_twistPrime I hI hPr u a

theorem lvQ_open (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hm : i < B.R.m) (b : (I.stp u a i).β) : ThetaOpen (lvQ I a i b) := by
  obtain ⟨al, hal⟩ := Option.isSome_iff_exists.1 (b.2.2 hm)
  show ThetaOpen (b.1.elim _ _)
  rw [hal]
  exact thetaOpen_levQ (hI.idx_ok a) (q_disj I hI a) i al

end Main

end GlobalTheory.Mem.Col2.ChExM

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChExM

open GlobalTheory.Mem.Col2.ChEx

section Main2

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem inv_norm (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β)
    (q q' : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (h : bar q = bar q') (h' : cqOf q = cqOf q') :
    bar (rpT I u a i ((I.stp u a i).cl b q)) = bar (rpT I u a i ((I.stp u a i).cl b q')) ∧
    cqOf (rpT I u a i ((I.stp u a i).cl b q)) = cqOf (rpT I u a i ((I.stp u a i).cl b q')) := by
  have hd := q_disj I hI a
  rw [← cosetIn_iff hd (hqG hPr)]
  by_cases hi : i + 1 = B.R.m
  swap
  · exact cos_of_neT I hi _ _
  have hm := B.R.two_le_m
  have key := @prefRep_normal _ _ _ _ ((I.stp0 u a i).actD b) ⟨cosetIn q⟩ (fun q' => cosetIn q') (I.pref u a i b) fun p =>
    ⟨fun h => h.2.1 hi, fun h => ⟨fun h0 => by omega, fun _ => h, fun h0 => by omega⟩⟩
  refine (key q).trans (Eq.trans ?_ (key q').symm)
  congr 1
  funext r
  refine propext (exists_congr fun g => ?_)
  have : cosetIn (ya (lvG I a i b) (lvQ I a i b) g q) = cosetIn (ya (lvG I a i b) (lvQ I a i b) g q') := by
    rw [cosetIn_iff hd (hqG hPr)]
    refine ⟨?_, ?_⟩
    · funext w
      rw [bar_ya, bar_ya, h]
    · funext P
      rw [cqOf_acts hd, cqOf_acts hd, h']
  exact this ▸ Iff.rfl

end Main2

end GlobalTheory.Mem.Col2.ChExM

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChExM

open GlobalTheory.Mem.Col2.ChEx

section Main3

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

set_option maxHeartbeats 2000000 in

theorem chart_of (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (Q' : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (hm : i < B.R.m)
    (hQ' : ∀ v, v ∈ Q' ↔ I.UnderQ a v) (k : GA B (B.R.N i))
    (k1 : ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i))
    (k2 : ∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v →
      (a = I.mu0 ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) k = 1)
    (k3 : ∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
      HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N i)).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0))
    (g : (I.stp u a i).Cl → GA B (B.R.N i)) (hg : ∀ c, PtOf (g c) (extTo I.SQ ((I.stp u a i).rep c).1.1))
    (c₀ : (I.stp u a i).Cl) (p : (I.stp u a i).Cl → Prop)
    (hp : ∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rpT I u a i c) = bar (rpT I u a i c₀) ∧ cqOf (rpT I u a i c) = cqOf (rpT I u a i c₀)) :
    ∃ (K : LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q') i hi (fun c : {c // p c} => (I.chain l u a).stab i c.1)
        (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)))
      (q : QLoc B.sp.cm (B.R.N i) (I.Q a) (cutQ (lvQ I a i c₀.1) (cqOf (rpT I u a i c₀)))),
      K.lev.Lb = baseLb B.fields.E (B.R.N i) ((B.primes X).vT u) ∧
      (id K.lev.U : Subgroup (GA B (B.R.N i))) =
        (levUQ B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (chG (lvG I a i c₀.1) (bar (rpT I u a i c₀))) q).map
          (MulAut.conj k).toMonoidHom ∧
      (∀ (x : K.lev.U) (z : levUQ B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (chG (lvG I a i c₀.1) (bar (rpT I u a i c₀))) q),
        (id x.1 : GA B (B.R.N i)) = k * z.1 * k⁻¹ →
        K.lev.chi x = ((levTyp (chLam (X := B.fields) B.embLL (lvG I a i c₀.1) (bar (rpT I u a i c₀)))).comp (Subgroup.inclusion (levUQ_le q _)) *
          (chiQ q _ B.embLL)⁻¹ : levUQ B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (chG (lvG I a i c₀.1) (bar (rpT I u a i c₀))) q →* ℂˣ) z) ∧
      (∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1) ∧
      (∀ c, (K.y c).1 = g c.1 * k⁻¹) ∧ ∀ c a', (K.stabI c a').1 = (I.stp u a i).gam c.1.1 a'.1 := by
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  obtain ⟨hg1, -, hl⟩ := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z).2.2.2 i hi
  have hf : B.fields.f = B.R.f := (hPr.vT_card u).symm.trans (l.lev u a).card_ST
  have hd := q_disj I hI a
  have hq := hqG hPr
  have hact := cqOf_acts (R := B.R) (cst := I.cst a) (u := u) (j := i) hd
  have hdet := cqOf_det (R := B.R) (cst := I.cst a) (u := u) (j := i) hd hq
  have hO : ThetaOpen (cutQ (lvQ I a i c₀.1) (cqOf (rpT I u a i c₀))) :=
    thetaOpen_cutQ (B.R.N i) _ (lvQ_open I hI u a i hm c₀.1) _ (cqOf_form hd (rpT I u a i c₀))
  have hcj := q_conj I hI a
  let q := qbLoc B.sp.cm (cutQ (lvQ I a i c₀.1) (cqOf (rpT I u a i c₀))) hcj hO
  have k3' : ∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
      HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N i)).1 r j))
      (if j = r then ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) else 0) := fun P r j hr => by
    have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u))) := by
      have h0 : Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u)) ≠ 0 := fun h0 =>
        (basePi_of_ok (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr u).conj_notMem P.2 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      exact @Ne.isUnit (Res P.1) _ _ h0
    have e : ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) =
        Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) := by
      unfold diaT
      rw [dif_pos hu]
      rfl
    rw [e]
    exact k3 P r j hr
  obtain ⟨hkU, hkV, hkL, hkT⟩ := k_facts (F := B.host.F) (E := B.host.E) B.sp.cm (B.R.N i) (basePi_of_ok hX hPr u) k (diaT (Pr := B.primes X) u) k1 k3'
  have hbad : badQ (I.rec7 l Z) Q' = badQ' (F := B.host.F) (B.primes X).vGs (I.Q a) := by
    refine Set.ext fun v => or_congr (plUnder_vGs (X := B.fields) B.sp.cm hPr v).symm ?_
    refine (hQ' v).trans ⟨?_, ?_⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
    · rintro ⟨P, rfl⟩
      exact ⟨P.1, P.2, rfl⟩
  have hkO : ∀ v, v ∉ badQ' (F := B.host.F) (B.primes X).vGs (I.Q a) → (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1 := by
    intro v hv hT
    rw [← hbad] at hv
    refine k2 v hT (fun h => hv (Or.inr ((hQ' v).2 h))) (Or.inr fun j hj => hv (Or.inl ?_))
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr hj
  have hpt : ∀ c, g c ∈ UAd B.sp.cm (B.R.N i) ∧ FrExact q (g c) (rpT I u a i c).1.1 := fun c =>
    frExact_of_isPtOf B.sp.cm (B.R.N i) q hcj (IsPtOf.of_extTo (q_sub_SQ I a) (Finset.disjoint_right.2 fun P h => hd P h) (hg c))
  obtain ⟨lev, Y, SI, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := chartQ_exists (F := B.host.F) (E := B.host.E) B.sp.cm (B.R.N i)
    (chH (X := B.fields) (lvG I a i c₀.1) (bar (rpT I u a i c₀))) (f := B.R.f)
    (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (hPr.vT_norm u P hP : Ideal.absNorm P.asIdeal = B.T u)) (rls_T_notUnder hPr u)
    (hf ▸ colBase_index (X := B.fields) B.sp.cm (B.R.N i) hPr u) (chLam (X := B.fields) B.embLL (lvG I a i c₀.1) (bar (rpT I u a i c₀)))
    q (qbOpen _ _ hcj hO) (trace_not_mem_twistPrime_under I hI hPr u a) B.embLL k hkU hkV hkL hkT hkO
    (gramN (I.rec7 l Z) i hi) hg1 (badQ (I.rec7 l Z) Q') hbad
    (fun c : {c // p c} => (I.stp u a i).Stab c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))
    (fun c => (rpT I u a i c.1).1.1) (fun c => g c.1) (fun c => (hpt c.1).1) (fun c => (hpt c.1).2.over)
    (cls_bijQ (lvG I a i) (lvQ I a i) _ _ _ hact hdet (exists_pt_inv hd) (inv_norm I hI hPr u a i) c₀ p hp)
    (fun c => (hl u a).1 c.1)
    (fun c => stM (lvG I a i) (lvQ I a i) _ _ c.1) (fun c => stM_inj (lvG I a i) (lvQ I a i) _ _ ((l.ch u a).step i) c.1)
    (fun c γ => stM_rangeQ (lvG I a i) (lvQ I a i) _ _ _ hact hdet c.1 c₀.1 ((hp c.1).1 c.2).1 _ ((hp c.1).1 c.2).2.1 _ ((hp c.1).1 c.2).2.2 γ)
    (qb_chr_root B.sp.cm (B.R.N i) _ hcj hO)
  exact ⟨⟨lev, Y, h1, h2, SI, h3, h4⟩, q, h5, h6, h7, h8, h9, h10⟩

end Main3

end GlobalTheory.Mem.Col2.ChExM

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChExM

open GlobalTheory.Mem.Col2.ChEx

section AutomorphyRankFourMain

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

set_option maxHeartbeats 1000000 in
theorem lev_at (hI : I.Ok) (hPr : (B.primes X).Ok) {u : B.Word} {a : I.ι} {i : ℕ} (c : (I.stp u a i).Cl) (b : (I.stp u a i).β) (hb : c.1 = b)
    (C : ∀ w : (B.primes X).vGs, Set (Fin (B.R.N i) → 𝓞 B.fields.E ⧸ w.1.asIdeal)) (hC : bar (rpT I u a i c) = C)
    (D : ∀ P : I.Q a, Set (Sp B.fields.E (B.R.N i))) (hD : cqOf (rpT I u a i c) = D)
    (q : QLoc B.sp.cm (B.R.N i) (I.Q a) (cutQ (lvQ I a i b) D)) {g s : GA B (B.R.N i)} (hg : g ∈ UAd B.sp.cm (B.R.N i))
    (hx : g * s ∈ UAd B.sp.cm (B.R.N i)) (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i)
    (e : FrExact q g (rpT I u a i c).1.1) (e' : FrExact q (g * s) p) :
    s ∈ levUQ B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (chG (lvG I a i b) C) q ↔
      ∃ κ : (I.stp u a i).G c.1, (I.stp u a i).gam c.1 κ = 1 ∧ ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1 = p ∧
        cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) := by
  subst hb
  have hd := q_disj I hI a
  refine (lev_iffQ B.sp.cm cqOf (cqOf_acts hd) (lvG I a i c.1) (lvQ I a i c.1) (rpT I u a i c) C hC D hD q hg hx p e e').trans ?_
  exact exists_congr fun κ => and_congr Iff.rfl (and_congr Iff.rfl (cosetIn_iff hd (hqG hPr) _ _).symm)

set_option maxHeartbeats 1000000 in
theorem chr_at {u : B.Word} {a : I.ι} {i : ℕ} (c : (I.stp u a i).Cl) (b : (I.stp u a i).β) (hb : c.1 = b)
    (C : ∀ w : (B.primes X).vGs, Set (Fin (B.R.N i) → 𝓞 B.fields.E ⧸ w.1.asIdeal))
    (D : ∀ P : I.Q a, Set (Sp B.fields.E (B.R.N i)))
    (q : QLoc B.sp.cm (B.R.N i) (I.Q a) (cutQ (lvQ I a i b) D)) {g : GA B (B.R.N i)}
    (z : levUQ B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (chG (lvG I a i b) C) q)
    (hg : g ∈ UAd B.sp.cm (B.R.N i)) (κ : (I.stp u a i).G c.1) (h1 : (I.stp u a i).gam c.1 κ = 1)
    (e : FrExact q g (rpT I u a i c).1.1) (e' : FrExact q (g * z.1) ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1) :
    ((((levTyp (chLam (X := B.fields) B.embLL (lvG I a i b) C)).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ B.embLL)⁻¹ :
      levUQ B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (chG (lvG I a i b) C) q →* ℂˣ) z : ℂˣ) : ℂ) =
      B.embLL (((I.stp u a i).chr c.1 κ : B.LLˣ) : B.LL) := by
  subst hb
  have h := chr_eqQ (X := B.fields) B.sp.cm B.embLL (lvG I a i c.1) (lvQ I a i c.1) (rpT I u a i c) C D q z hg κ h1 e e'
  rw [h]
  rfl

set_option maxHeartbeats 2000000 in

theorem exists_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∀ k : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i), GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i k → ∃ K : ∀ β : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)), I.Reads u a i (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u a Q i hi _ hm hQ k hk
  have hPr := l.pr
  have hd := q_disj I hI a
  have hq := hqG hPr
  have hcj := q_conj I hI a
  have key : ∀ c c', GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c' ↔
      c.1 = c'.1 ∧ cosetIn ((I.stp u a i).rep c) = cosetIn ((I.stp u a i).rep c') := fun c c' =>
    Subtype.ext_iff.trans Prod.ext_iff
  have onto : Function.Surjective (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i) := fun β => ⟨β.2.choose, Subtype.ext β.2.choose_spec⟩
  choose s hs using onto
  have hp : ∀ β c, GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β ↔
      c.1 = (s β).1 ∧ bar (rpT I u a i c) = bar (rpT I u a i (s β)) ∧ cqOf (rpT I u a i c) = cqOf (rpT I u a i (s β)) := fun β c => by
    rw [← cosetIn_iff hd hq]
    conv_lhs => rw [← hs β]
    exact key c (s β)
  choose g hg using fun c : (I.stp u a i).Cl => GlobalTheory.T.exists_adelicPoint_decoratedLattice_allTwists I hI u _ (extTo I.SQ ((I.stp u a i).rep c).1.1)
  choose K q K1 K2 K3 K4 K5 K6 using fun β => chart_of I hI hP l Z u a Q i hi hm hQ (k β) (hk.std β) (hk.off β) (hk.T β) g hg (s β)
    (fun c => GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β) (hp β)
  have hy : ∀ c, (id ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1 : GA B (B.R.N i)) = g c * (k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c))⁻¹ := fun c => K5 _ _
  have hpt : ∀ c, PtOf (g c) ((I.stp u a i).rep c).1.1 := fun c =>
    IsPtOf.of_extTo (q_sub_SQ I a) (Finset.disjoint_right.2 fun P h => hd P h) (hg c)
  have hmove : ∀ c (x : GA B (B.R.N i)), (id ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1 : GA B (B.R.N i)) * x * k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c) =
      g c * ((k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c))⁻¹ * x * k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)) := fun c x => by
    rw [hy c]
    group
  have hU : ∀ β (x : GA B (B.R.N i)), x ∈ (id (K β).lev.U : Subgroup (GA B (B.R.N i))) ↔ _ := fun β x =>
    Iff.of_eq (congrArg (fun S : Subgroup (GA B (B.R.N i)) => x ∈ S) (K2 β))
  refine ⟨K, ⟨key, fun β => ⟨_, hs β⟩, fun β x => ?_, hk.std, hk.off, hk.T, fun c => ?_, fun c x r h => ?_, fun c x κ h1 h2 => ?_, fun c a' => K6 _ _ _⟩, K4⟩
  · exact (K1 β ▸ Iff.rfl : x ∈ (K β).lev.Lb ↔ x ∈ baseLb B.fields.E (B.R.N i) ((B.primes X).vT u)).trans (mem_baseLb (B := B) (X := X) hPr u _ x)
  · show PtOf ((id ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1 : GA B (B.R.N i)) * k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)) _
    rw [hy c, inv_mul_cancel_right]
    exact hg c
  · have h' : PtOf (g c * ((k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c))⁻¹ * x * k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c))) r := by
      rw [← hmove c x]; exact h
    have e := frExact_of_isPtOf B.sp.cm (B.R.N i) (q (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)) hcj (hpt c)
    have e' := frExact_of_isPtOf B.sp.cm (B.R.N i) (q (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)) hcj h'
    have hc := (hp (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c) c).1 rfl
    refine ((hU _ x).trans (mem_map_conj _ _ _)).trans ?_
    exact lev_at I hI hPr c _ hc.1 _ hc.2.1 _ hc.2.2 _ e.1 e'.1 r e.2 e'.2
  · have hz := (mem_map_conj _ _ _).1 ((hU _ x.1).1 x.2)
    have h2' : PtOf (g c * ((k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c))⁻¹ * x.1 * k (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)))
        ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1 := by
      rw [← hmove c x.1]; exact h2
    have e := frExact_of_isPtOf B.sp.cm (B.R.N i) (q (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)) hcj (hpt c)
    have e' := frExact_of_isPtOf B.sp.cm (B.R.N i) (q (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)) hcj h2'
    have hc := (hp (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c) c).1 rfl
    have h3 := K3 (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c) x ⟨_, hz⟩ (by simp only [id, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one])
    refine (congrArg Units.val h3).trans ?_
    exact chr_at I c _ hc.1 _ _ _ ⟨_, hz⟩ e.1 κ h1 e.2 e'.2

end AutomorphyRankFourMain

end GlobalTheory.Mem.Col2.ChExM
end
end
end
end
end
end
end
