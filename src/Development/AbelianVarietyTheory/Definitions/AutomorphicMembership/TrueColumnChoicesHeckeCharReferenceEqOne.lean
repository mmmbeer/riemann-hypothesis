import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Formalism.LocalToGlobal.KernelLattices.ThDistC

section
noncomputable section

namespace GlobalTheory.Mem.Col2.Th

open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

variable {R : Ranks} (H : Host R) {ι : Type} [Fintype ι] (emb : ι → H.E →+* ℂ)

abbrev Lt (N : ℕ) : Type := Submodule (𝓞 H.E) (Fin N → H.E)

abbrev VC (ι : Type) (N N' : ℕ) : Type := ι → Fin N' → Fin N → ℂ

def lamOf (cc : Ideal (𝓞 H.K)) (δ : ℂ) : AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * H.φ₀ (((c : H.K) : H.E))}

def IsDiscriminantTwelfthRootOfIdealLattice (cc : Ideal (𝓞 H.K)) (δ : ℂ) : Prop := δ ^ 12 = TaylorLogMetric.discr (lamOf H cc 1)

def IsTwoTorsionPointUnkilled (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2) * t ∉ Λ ∧
    ((1 - Complex.I * (Real.sqrt H.d : ℂ)) / 2) * t ∉ Λ

def stdL (N : ℕ) : Lt H N := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 H.E) H.E)

def homL {N N' : ℕ} (L : Lt H N) (L' : Lt H N') : Submodule (𝓞 H.E) (Matrix (Fin N') (Fin N) H.E) :=
  Submodule.span (𝓞 H.E) {A | ∀ x ∈ L, A.mulVec x ∈ L'}

def YYl {N N' : ℕ} (L : Lt H N) (L' : Lt H N') : Submodule (𝓞 H.E) (Matrix (Fin N') (Fin N) H.E) :=
  Submodule.span (𝓞 H.E) {B | ∃ a ∈ (H.AA0 : Submodule (𝓞 H.E) H.E), ∃ A ∈ homL H L L', B = a • A}

def La (Λ : AddSubgroup ℂ) {N N' : ℕ} (L : Lt H N) (L' : Lt H N') : AddSubgroup (VC ι N N') :=
  AddSubgroup.closure {z | ∃ w ∈ Λ, ∃ A ∈ YYl H L L', z = w • (fun τ i j => emb τ (A i j) : VC ι N N')}

def Hf (Λ : AddSubgroup ℂ) {N N' : ℕ} (z w : VC ι N N') : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (TaylorLogMetric.area Λ : ℂ)

def al (Λ : AddSubgroup ℂ) {N N' : ℕ} (x : VC ι N N') : ℂ :=
  (-1 : ℂ) ^ (round (Real.sqrt H.d / 2 * (Hf Λ x x).re))

def U (Λ : AddSubgroup ℂ) {N N' : ℕ} (x : VC ι N N') (G : VC ι N N' → ℂ) : VC ι N N' → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * Hf Λ z x - (Real.pi : ℂ) * Hf Λ x x / 2)

def Iop (Λ : AddSubgroup ℂ) {N N' : ℕ} (La₁ La₂ : AddSubgroup (VC ι N N')) (G : VC ι N N' → ℂ) : VC ι N N' → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al H Λ ((Quotient.out q : La₂) : VC ι N N') * U Λ ((Quotient.out q : La₂) : VC ι N N') G z

def detId {N : ℕ} (L L' : Lt H N) : Submodule (𝓞 H.E) H.E :=
  Submodule.span (𝓞 H.E) {x | ∃ A : Matrix (Fin N) (Fin N) H.E, (∀ v ∈ L, A.mulVec v ∈ L') ∧ x = A.det}

def lamMM (Λ : AddSubgroup ℂ) : AddSubgroup (ι → ℂ) :=
  AddSubgroup.closure {z | ∃ w ∈ Λ, ∃ a ∈ H.AA0, z = fun τ => w * emb τ a}

def mmM (M : IntermediateField ℚ ℂ) [NumberField M] : Submodule (𝓞 M) (ι → M) :=
  Submodule.span (𝓞 M) {v | ∃ a ∈ (H.AA0 : Submodule (𝓞 H.E) H.E), v = fun τ => TaylorLogMetric.liftM M (emb τ a)}

def ellT (M : IntermediateField ℚ ℂ) [NumberField M] (τ : ι) : Submodule (𝓞 M) M :=
  (mmM H emb M).comap (LinearMap.single (𝓞 M) (fun _ : ι => (M : Type)) τ)

def IsDgen (cD : ι → ℂ) : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), (∀ τ x, emb τ x ∈ M) ∧ ∀ τ, ∃ s : M, (s : ℂ) = cD τ ∧
    ellT H emb M τ = Submodule.span (𝓞 M) {s}

def SplitK (p : ℕ) : Prop := p = 2 ∨ jacobiSym (-(H.d : ℤ)) p = 1

variable (ι) in

abbrev IsoK : Type := IsoKG H.K H.E H.conj ι

variable {H} in

def AtP (γ : IsoK H ι) (p : ℕ) : Prop :=
  (∀ x : Fin 4 → H.E, (∀ a, x a ∈ H.AA0) → ∃ s : ℕ, Nat.Coprime s p ∧
    ∀ w, (s : H.K) * γ.g x w ∈ (algebraMap (𝓞 H.K) H.K).range) ∧
  ∀ v : Fin 4 × ι → H.K, (∀ w, v w ∈ (algebraMap (𝓞 H.K) H.K).range) →
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : H.E) * γ.g.symm v a ∈ H.AA0

variable {H} in

def detRel (γ γ₀ : IsoK H ι) : H.K :=
  LinearMap.det ((γ₀.g.symm.trans γ.g : (Fin 4 × ι → H.K) ≃ₗ[H.K] _) : (Fin 4 × ι → H.K) →ₗ[H.K] (Fin 4 × ι → H.K))

variable {H} in

structure KapIn (γ₀ : IsoK H ι) where
  pp : ℕ → IsDedekindDomain.HeightOneSpectrum (𝓞 H.K)
  pp_over : ∀ p, p.Prime → SplitK H p → ((p : ℕ) : 𝓞 H.K) ∈ (pp p).asIdeal
  pi : ℕ → 𝓞 H.K
  pi_gen : ∀ p, p.Prime → SplitK H p → (pp p).asIdeal ^ classNumber H.K = Ideal.span {pi p}
  gaP : ℕ → IsoK H ι
  gaP_at : ∀ p, p.Prime → SplitK H p → AtP (gaP p) p
  rt : ℕ → ℂ
  rt_pow : ∀ p, p.Prime → SplitK H p → rt p ^ (2 * classNumber H.K)
    = H.φ₀ (((pi p : 𝓞 H.K) : H.K) : H.E) / H.φ₀ (H.conj (((pi p : 𝓞 H.K) : H.K) : H.E))

variable {H} in

def KapIn.yP {γ₀ : IsoK H ι} (k : KapIn γ₀) (p : ℕ) : ℤ :=
  -WithZero.log ((k.pp p).valuation H.K (detRel (k.gaP p) γ₀))

variable {H} in

def KapIn.kappa {γ₀ : IsoK H ι} (k : KapIn γ₀) : ℂ :=
  ∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK H p}, k.rt p ^ (-(k.yP p))

structure VacIn (cc : Ideal (𝓞 H.K)) (δ : ℂ) where
  L : PeriodPair
  lat : L.lattice.toAddSubgroup = lamOf H cc δ
  ω₀ : ℂ
  t0 : IsTwoTorsionPointUnkilled H (lamOf H cc δ) (ω₀ / 2)
  γ₀ : IsoK H ι
  gC : (Fin 4 × ι → ℂ) ≃ₗ[ℂ] (Fin 4 × ι → ℂ)
  gC_spec : ∀ x : Fin 4 → H.E, gC (fun w => emb w.2 (x w.1)) = fun w => H.φ₀ ((γ₀.g x w : H.K) : H.E)
  kc : KapIn γ₀

def chiFac (χ : Submodule (𝓞 H.E) H.E → ℂ) (N N' : ℕ) (L : Lt H N) (L' : Lt H N') : ℂ :=
  χ (detId H (stdL H N) L) ^ (((N' / 2 : ℕ) : ℤ)) * χ (detId H (stdL H N') L') ^ (-((N / 2 : ℕ) : ℤ))

def perAA (cc : Ideal (𝓞 H.K)) : Submodule (𝓞 H.E) H.E :=
  Submodule.span (𝓞 H.E) {r | ∃ c ∈ cc, ∃ t ∈ H.AA0, r = (((c : 𝓞 H.K) : H.K) : H.E) * t}

namespace VacIn

variable {H emb} {cc : Ideal (𝓞 H.K)} {δ : ℂ} (V : VacIn H emb cc δ)

def thMM : (ι → ℂ) → ℂ := thM V.L V.ω₀ (Real.sqrt H.d / 2) (lamMM H emb (lamOf H cc δ)) V.gC V.kc.kappa

def thZero (N N' : ℕ) : VC ι N N' → ℂ := tensPow V.thMM N N'

def thHalf (N N' : ℕ) (L : Lt H N) : VC ι N N' → ℂ :=
  Iop H (lamOf H cc δ) (La H emb (lamOf H cc δ) (stdL H N) (stdL H N')) (La H emb (lamOf H cc δ) L (stdL H N')) (V.thZero N N')

def thMoved (N N' : ℕ) (L : Lt H N) (L' : Lt H N') : VC ι N N' → ℂ :=
  Iop H (lamOf H cc δ) (La H emb (lamOf H cc δ) L (stdL H N')) (La H emb (lamOf H cc δ) L L') (V.thHalf N N' L)

def eNat (χ : Submodule (𝓞 H.E) H.E → ℂ) (N N' : ℕ) (L : Lt H N) (L' : Lt H N') : VC ι N N' → ℂ :=
  fun z => chiFac H χ N N' L L' * V.thMoved N N' L L' z

end VacIn

section Record

variable (D : D7)


theorem isDiscriminantTwelfthRoot_host_iff (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : IsDiscriminantTwelfthRootOfIdealLattice D.host cc δ ↔ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ := Iff.rfl






variable {D} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def KapIn.toRec {γ₀ : IsoK D.host D.what₂.Tau} (k : KapIn γ₀) : KapChoice (D := D) γ₀ :=
  ⟨k.pp, k.pp_over, k.pi, k.pi_gen, k.gaP, k.gaP_at, k.rt, k.rt_pow⟩

def KapIn.ofRec {γ₀ : IsoK D.host D.what₂.Tau} (k : KapChoice (D := D) γ₀) : KapIn γ₀ :=
  ⟨k.pp, k.pp_over, k.pi, k.pi_gen, k.gaP, k.gaP_at, k.rt, k.rt_pow⟩

def VacIn.toRec (V : VacIn D.host (TaylorLogMetric.embT D) cc δ) : Formalism.L2.Ker.Base D cc δ :=
  ⟨V.L, V.lat, V.ω₀, V.t0, V.γ₀, V.gC, V.gC_spec, V.kc.toRec⟩

def VacIn.ofRec (B : Formalism.L2.Ker.Base D cc δ) : VacIn D.host (TaylorLogMetric.embT D) cc δ :=
  ⟨B.L, B.lat, B.ω₀, B.t0, B.γ₀, B.gC, B.gC_spec, KapIn.ofRec B.kc⟩





end Record

example (Λ : AddSubgroup ℂ) {N N' : ℕ} (c : ℂ) (z w : VC ι N N') : Hf Λ (c • z) w = c * Hf Λ z w := by
  simp only [Hf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

example (Λ : AddSubgroup ℂ) {N N' : ℕ} (G : VC ι N N' → ℂ) : Iop H Λ ⊥ ⊥ G = G := by
  funext z
  have h0 : ∀ q : (⊥ : AddSubgroup (VC ι N N')) ⧸ (⊥ : AddSubgroup (VC ι N N')).addSubgroupOf ⊥,
      ((Quotient.out q : (⊥ : AddSubgroup (VC ι N N'))) : VC ι N N') = 0 := fun q => AddSubgroup.mem_bot.1 (Quotient.out q).2
  have hU : Unique ((⊥ : AddSubgroup (VC ι N N')) ⧸ (⊥ : AddSubgroup (VC ι N N')).addSubgroupOf ⊥) :=
    ⟨⟨QuotientAddGroup.mk 0⟩, fun q => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      rw [Subsingleton.elim x 0]
      rfl⟩
  simp only [Iop, h0, finsum_unique]
  simp [al, U, Hf]

theorem perAA_top : perAA H ⊤ = (H.AA0 : Submodule (𝓞 H.E) H.E) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, -, t, ht, rfl⟩
    exact (H.AA0 : Submodule (𝓞 H.E) H.E).smul_mem (algebraMap (𝓞 H.K) (𝓞 H.E) c) ht
  · intro t ht
    exact Submodule.subset_span ⟨1, trivial, t, ht, by simp⟩

end GlobalTheory.Mem.Col2.Th

end
end

section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr
open ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin unif ordF)
open scoped TensorProduct

section Reads

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def afIso : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E :=
  (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose

theorem afIso_tmul_one (x : E) : afIso F E (x ⊗ₜ[F] 1) = algebraMap E _ x :=
  (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.1 x

theorem mem_rInt_iff (y : AfE F E) : y ∈ RInt F E ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (afIso F E y P) ≤ 1 :=
  (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.1 y

theorem mem_suppAt_iff (v : HeightOneSpectrum (𝓞 F)) (y : (AfE F E)ˣ) :
    y ∈ suppAt E v ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ≠ v → afIso F E (y : AfE F E) P = 1 :=
  (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.1 v y

def finAf : Ideles E →* (AfE F E)ˣ :=
  Units.map (((afIso F E).symm : FiniteAdeleRing (𝓞 E) E →* AfE F E).comp
    (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)))

theorem afIso_finAf (a : Ideles E) : afIso F E (finAf F E a : AfE F E) = (a : AdeleRing (𝓞 E) E).2 :=
  (afIso F E).apply_symm_apply _

theorem finAf_surjective : Function.Surjective (finAf F E) := fun y =>
  ⟨Units.map ((MonoidHom.inr (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)).comp
    (afIso F E : AfE F E →* FiniteAdeleRing (𝓞 E) E)) y, Units.ext ((afIso F E).symm_apply_apply _)⟩

variable {F E} {K : Type} [Field K] (σ : K →+* ℂ)

def Reads (μ : Chr F E K) (ξ : HChar E) : Prop :=
  ∀ a : Ideles E, ((ξ.1 a : ℂˣ) : ℂ) = σ ((μ (finAf F E a) : Kˣ) : K)

variable {σ}

theorem Reads.unique {μ : Chr F E K} {ξ ξ' : HChar E} (h : Reads σ μ ξ) (h' : Reads σ μ ξ') : ξ = ξ' :=
  Subtype.ext (MonoidHom.ext fun a => Units.ext ((h a).trans (h' a).symm))

theorem Reads.inj {μ μ' : Chr F E K} {ξ : HChar E} (h : Reads σ μ ξ) (h' : Reads σ μ' ξ) : μ = μ' := by
  refine MonoidHom.ext fun y => ?_
  obtain ⟨a, rfl⟩ := finAf_surjective F E y
  exact Units.ext (σ.injective ((h a).symm.trans (h' a)))

variable (σ) in

theorem reads_one : Reads σ (1 : Chr F E K) (1 : HChar E) := fun a => by
  show ((1 : ℂˣ) : ℂ) = σ ((1 : Kˣ) : K)
  simp

theorem Reads.mul {μ μ' : Chr F E K} {ξ ξ' : HChar E} (h : Reads σ μ ξ) (h' : Reads σ μ' ξ') : Reads σ (μ * μ') (ξ * ξ') :=
  fun a => by
    show ((ξ.1 a * ξ'.1 a : ℂˣ) : ℂ) = σ ((μ (finAf F E a) * μ' (finAf F E a) : Kˣ) : K)
    rw [Units.val_mul, Units.val_mul, map_mul, h a, h' a]

theorem Reads.apply {μ : Chr F E K} {ξ : HChar E} (h : Reads σ μ ξ) (a : Ideles E) (y : (AfE F E)ˣ)
    (hy : afIso F E (y : AfE F E) = (a : AdeleRing (𝓞 E) E).2) : ((ξ.1 a : ℂˣ) : ℂ) = σ ((μ y : Kˣ) : K) := by
  have : y = finAf F E a := Units.ext ((afIso F E).injective (hy.trans (afIso_finAf F E a).symm))
  rw [this]
  exact h a

theorem Reads.orderDvd {μ : Chr F E K} {ξ : HChar E} (h : Reads σ μ ξ) {n : ℕ} (hn : μ ^ n = 1) : ξ.OrderDvd n := by
  refine Subtype.ext (MonoidHom.ext fun a => Units.ext ?_)
  have h1 : μ (finAf F E a) ^ n = 1 := congrArg (fun f : Chr F E K => f (finAf F E a)) hn
  show ((ξ.1 a ^ n : ℂˣ) : ℂ) = ((1 : ℂˣ) : ℂ)
  rw [Units.val_pow_eq_pow_val, h a, ← map_pow, ← Units.val_pow_eq_pow_val, h1]
  simp

end Reads

def chiId {L : Type} [Field L] [NumberField L] (χ : HChar L) (𝔞 : Submodule (𝓞 L) L) : ℂ :=
  ((∏ᶠ w : HeightOneSpectrum (𝓞 L), χ.val w ^ (ordSub w 𝔞).toNat : ℂˣ) : ℂ)

theorem chiId_ne_zero {L : Type} [Field L] [NumberField L] (χ : HChar L) (𝔞 : Submodule (𝓞 L) L) : chiId χ 𝔞 ≠ 0 :=
  Units.ne_zero _

theorem chiId_span_singleton {L : Type} [Field L] [NumberField L] (χ : HChar L) (u : Lˣ) :
    chiId χ (Submodule.span (𝓞 L) {(u : L)}) =
      ((∏ᶠ w : HeightOneSpectrum (𝓞 L), χ.val w ^ (ordF w u).toNat : ℂˣ) : ℂ) := by
  simp only [chiId, ordSub_span_singleton]

theorem chiId_one {L : Type} [Field L] [NumberField L] (χ : HChar L) : chiId χ 1 = 1 := by
  have h := chiId_span_singleton χ 1
  rw [Units.val_one, ← Submodule.one_eq_span] at h
  rw [h]
  simp [ordF]

theorem detId_std {R : Ranks} (H : Host R) (N : ℕ) : Th.detId H (Th.stdL H N) (Th.stdL H N) = 1 := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨A, hA, rfl⟩
    have h : ∀ i j, ∃ b : 𝓞 H.E, algebraMap (𝓞 H.E) H.E b = A i j := fun i j => by
      have h1 : (Pi.single j 1 : Fin N → H.E) ∈ Th.stdL H N := fun k _ => by
        by_cases e : k = j
        · subst e
          rw [Pi.single_eq_same]
          exact Submodule.one_le.1 le_rfl
        · rw [Pi.single_eq_of_ne e]
          exact Submodule.zero_mem _
      have h2 := Submodule.mem_one.1 (hA _ h1 i trivial)
      simpa using h2
    choose b hb using h
    have e : A = (algebraMap (𝓞 H.E) H.E).mapMatrix (Matrix.of b) := Matrix.ext fun i j => (hb i j).symm
    rw [e, ← RingHom.map_det]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  · exact Submodule.one_le.2 (Submodule.subset_span ⟨1, fun v hv => by simpa using hv, Matrix.det_one.symm⟩)

abbrev embT {R : Ranks} (H : Host R) (τ : Tau R) : H.E →+* ℂ := H.emb (τ : R.GG)

structure AmbIn {R : Ranks} (H : Host R) where

  δ : ℂ

  V : Th.VacIn H (embT H) ⊤ δ

  cD : Tau R → ℂ

structure AmbIn.Ok {R : Ranks} {H : Host R} (J : AmbIn H) : Prop where
  delta : Th.IsDiscriminantTwelfthRootOfIdealLattice H ⊤ J.δ
  dgen : Th.IsDgen H (embT H) J.cD

def AmbIn.amb (B : Base) (J : AmbIn B.host) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) : Amb B.fields where
  σ₀ := B.embLL
  δ := J.δ
  d := B.host.d
  sc := (TaylorLogMetric.area (Th.lamOf B.host ⊤ J.δ))⁻¹
  AA := Th.perAA B.host ⊤
  cD := J.cD
  e a b N N' := J.V.eNat χ a b N N'
  chiF a b N N' := Th.chiFac B.host χ a b N N'

theorem AmbIn.δ_ne_zero {R : Ranks} {H : Host R} (J : AmbIn H) : J.δ ≠ 0 := by
  intro h
  have h1 : J.V.L.ω₁ ∈ Th.lamOf H ⊤ J.δ := by
    rw [← J.V.lat]
    exact J.V.L.ω₁_mem_lattice
  have h2 : Th.lamOf H ⊤ J.δ ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨c, -, rfl⟩
    simp [h]
  exact J.V.L.indep.ne_zero 0 (AddSubgroup.mem_bot.1 (h2 h1))

def duStarOf {R : Ranks} (H : Host R) (hc : Tau R → HCParam R) : ℝ :=
  (letI := H.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm H.E R.k) (StandardLattice.stdLat H.E R.k)) *
    (StandardLattice.idxColLoc (H.g 0) R.k ^ R.f * StandardLattice.idxColLoc (H.g 1) R.k ^ R.f) *
    ∏ τ, StandardLattice.dimV fun i => (((hc τ).u i : ℚ) : ℝ)

structure ColIn (B : Base) (X : PreX B.toPre) where

  C : HFrame B.host fun j τ => (B.hc τ).e j

  Ch : Chars B.fields (B.primes X) B.R.m

  sel : HeightOneSpectrum (𝓞 B.fields.F) → HeightOneSpectrum (𝓞 B.fields.E)

  S : Set ℕ

  ι : Type
  [finι : Fintype ι]

  tup : ι → Tup B.fields.F B.fields.E B.fields.K S
  tup_inj : Function.Injective tup

  mu0 : ι

  muStar : ι

  muStar' : ι
  trueColumn_tuple_trivial_eq_one : tup mu0 = 1

  xi : ι → HChar B.host.E

  cst : ∀ a, LocCst B.fields (rowSG (B.primes X) sel (tup a))

  idx : ∀ a, ChIdx B.fields (B.primes X) B.R (QE sel (tup a : Chr B.fields.F B.fields.E B.fields.K))

  J : AmbIn B.host

attribute [instance] ColIn.finι

namespace ColIn

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

def glob : ChGlob B.fields B.R.m where
  σ₀ := B.embLL
  xi0 := B.host.xi0
  mu0 := I.C.mu0

def chi : Submodule (𝓞 B.host.E) B.host.E → ℂ := chiId I.C.chiPsi

def A : Amb B.fields := I.J.amb B I.chi

abbrev Q (a : I.ι) : Finset (HeightOneSpectrum (𝓞 B.fields.E)) := QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K)

open Classical in

def SQ : Finset (HeightOneSpectrum (𝓞 B.host.E)) := Finset.univ.biUnion I.Q

abbrev dat : Dat := B.dat X I.Ch

structure Ok : Prop where

  spaces : letI := B.host.cmStar; DiagSpaces B.sp
  ch_ok : I.Ch.Ok

  ch_tied : I.Ch.Tied B.embLL (fun j τ => (B.hc τ).e j) I.C.mu0 I.C.eta

  weil : I.Ch.WeilTied B.embLL B.host.xi0

  pibar : ∀ k w, w ∈ (B.primes X).vG k ↔ I.C.P.Div k w
  sel_ok : IsSel B.fields I.sel

  T_mem : ∀ u, B.T u ∈ I.S

  g_mem : ∀ i, B.host.g i ∈ I.S

  ram_mem : ∀ p : ℕ, p.Prime → p ∣ B.host.condN → p ∈ I.S

  xi_reads : ∀ a, Reads B.embLL (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.xi a)

  xi_star : I.xi I.muStar = I.C.del
  xi_star' : I.xi I.muStar' = I.C.del'

  sharp : ∀ a, (I.cst a).sharp = true

  idx_ok : ∀ a, (I.idx a).Ok I.Ch I.sel (I.tup a) (I.cst a) I.glob (B.R.m - 2)
  amb_ok : I.J.Ok

  duStar : ∀ u, (B.duStar u : ℝ) = duStarOf B.host (B.hcW u)

theorem glob_σ₀ : I.glob.σ₀ = B.embLL := rfl



theorem A_σ₀ : I.A.σ₀ = B.embLL := rfl

theorem A_δ : I.A.δ = I.J.δ := rfl

theorem A_cD : I.A.cD = I.J.cD := rfl

theorem A_AA : I.A.AA = (B.host.AA0 : Submodule (𝓞 B.host.E) B.host.E) := Th.perAA_top B.host

theorem Q_subset_SQ (a : I.ι) : I.Q a ⊆ I.SQ := by
  classical
  intro P hP
  unfold SQ
  convert Finset.mem_biUnion.2 ⟨a, Finset.mem_univ a, hP⟩

theorem mem_SQ {P : HeightOneSpectrum (𝓞 B.host.E)} : P ∈ I.SQ ↔ ∃ a, P ∈ I.Q a := by
  unfold SQ
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]

theorem twistPrimes_reference_tuple_eq_empty : I.Q I.mu0 = ∅ := by
  have h : Qprime (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := by
    rw [I.trueColumn_tuple_trivial_eq_one]
    ext v
    simp [Qprime]
  unfold Q QE
  simp [h]

theorem exists_of_mem_Q {a : I.ι} {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ I.Q a) :
    ∃ v ∈ Qprime (I.tup a : Chr B.fields.F B.fields.E B.fields.K), I.sel v = P ∧ GoodPl B.fields.E I.S v := by
  classical
  unfold Q QE at hP
  split_ifs at hP with h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    rw [Set.Finite.mem_toFinset] at hv
    refine ⟨v, hv, rfl, by_contra fun hg => hv ?_⟩
    have h2 := (Subgroup.mem_inf.1 (I.tup a).2).2
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 v) hg
  · simp at hP

variable {I}

theorem Ok.trueColumnChoices_heckeChar_reference_eq_one (h : I.Ok) : I.xi I.mu0 = 1 := by
  have h1 := h.xi_reads I.mu0
  rw [I.trueColumn_tuple_trivial_eq_one] at h1
  exact h1.unique (reads_one _)

theorem Ok.xi_inj (h : I.Ok) : Function.Injective I.xi := fun a b hab =>
  I.tup_inj (Subtype.ext ((h.xi_reads a).inj (hab ▸ h.xi_reads b)))

theorem Ok.fromHecke (h : I.Ok) : I.Ch.FromHecke B.wts B.embLL := ⟨I.C.mu0, I.C.eta, h.ch_tied⟩

theorem Ok.mem_of_dvd_QSq (h : I.Ok) {p : ℕ} (hp : p.Prime) (hd : p ∣ B.host.QS * B.host.q) : p ∈ I.S :=
  h.ram_mem p hp (hd.mul_right _)

theorem Ok.mem_of_dvd_QS (h : I.Ok) {p : ℕ} (hp : p.Prime) (hd : p ∣ B.host.QS) : p ∈ I.S :=
  h.mem_of_dvd_QSq hp (hd.mul_right _)

theorem Ok.small_mem (h : I.Ok) {p : ℕ} (hp : p ∈ B.host.small) : p ∈ I.S :=
  h.mem_of_dvd_QS (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

theorem Ok.two_q_d_mem (h : I.Ok) : 2 ∈ I.S ∧ B.host.q ∈ I.S ∧ B.host.d ∈ I.S :=
  ⟨h.mem_of_dvd_QS Nat.prime_two ((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans B.host.tower_dvd),
    h.mem_of_dvd_QSq B.host.hyp.1 (dvd_mul_left _ _), h.ram_mem _ B.host.hyp.2.1 (dvd_mul_left _ _)⟩

theorem Ok.hm (h : I.Ok) : B.R.m = (B.R.m - 2) + 2 := (h.idx_ok I.mu0).hm

end ColIn

section Record

variable (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W) (G : GJStage B C)

def seamOf : Seam (assemble B C W V S N G) B.fields where
  iE := RingEquiv.refl _
  iT := Equiv.refl _
  σ₀ := B.embLL

theorem seamOf_ok : (seamOf B C W V S N G).Ok :=
  ⟨fun τ x => DFunLike.congr_fun (B.fields_embC τ) x, fun x => B.fields_star x⟩

theorem seamOf_lat {n : ℕ} (M : Submodule (𝓞 B.host.E) (Fin n → B.host.E)) : (seamOf B C W V S N G).lat M = M := by
  have h : (seamOf B C W V S N G).lat M = Submodule.span (𝓞 B.host.E) (id '' (M : Set (Fin n → B.host.E))) := rfl
  rw [h, Set.image_id, Submodule.span_eq]

def AmbIn.toRec (J : AmbIn B.host) : Formalism.L2.Ker.Base (assemble B C W V S N G) ⊤ J.δ :=
  Th.VacIn.toRec (D := assemble B C W V S N G) J.V

theorem AmbIn.amb_eq_ambOf (J : AmbIn B.host) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) :
    J.amb B χ = ambOf (seamOf B C W V S N G) (J.toRec B C W V S N G) χ J.cD := by
  unfold ambOf
  simp only [seamOf_lat]
  rfl

theorem AmbIn.ok_iff (J : AmbIn B.host) :
    J.Ok ↔ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (assemble B C W V S N G) ⊤ J.δ ∧ IsDgen (assemble B C W V S N G) J.cD :=
  ⟨fun h => ⟨h.delta, h.dgen⟩, fun h => ⟨h.1, h.2⟩⟩


end Record

example {B : Base} {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (v : HeightOneSpectrum (𝓞 B.host.E))
    (hv : Formalism.L2.Host.OverP B.host B.host.pde v) : I.muStar ≠ I.mu0 := by
  intro e
  have h1 : I.C.del = 1 := by rw [← h.xi_star, e, h.trueColumnChoices_heckeChar_reference_eq_one]
  have h2 := (I.C.isDel.ine v hv 1).1 fun x _ => by rw [h1]; simp
  omega

example {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K] (σ : K →+* ℂ)
    (μ : Chr F E K) (ξ : HChar E) (h : Reads σ μ ξ) (a : Ideles E) (ha : (a : AdeleRing (𝓞 E) E).2 = 1) : ξ.1 a = 1 := by
  apply Units.ext
  rw [h.apply a 1 (by rw [ha, Units.val_one, map_one])]
  simp

example {R : Ranks} (H : Host R) (χ : HChar H.E) (N N' : ℕ) : Th.chiFac H (chiId χ) N N' (Th.stdL H N) (Th.stdL H N') = 1 := by
  simp [Th.chiFac, detId_std, chiId_one]

end GlobalTheory.Mem.Col2

end
end
