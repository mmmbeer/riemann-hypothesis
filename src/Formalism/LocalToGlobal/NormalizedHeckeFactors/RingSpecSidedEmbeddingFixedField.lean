import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

section
noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace Formalism.L2.NC

section hecke

variable {E : Type} [Field E] [NumberField E]

@[ext]
structure HC (E : Type) [Field E] [NumberField E] where
  χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ
  cont : Continuous χ
  triv : ∀ a : Eˣ, χ (Units.map (algebraMap E (AdeleRing (𝓞 E) E)).toMonoidHom a) = 1

instance : Mul (HC E) where
  mul χ ψ := ⟨χ.χ * ψ.χ, χ.cont.mul ψ.cont, fun a => by rw [MonoidHom.mul_apply, χ.triv a, ψ.triv a, one_mul]⟩

instance : Inv (HC E) where
  inv χ := ⟨χ.χ⁻¹, χ.cont.inv, fun a => by rw [MonoidHom.inv_apply, χ.triv a, inv_one]⟩

instance : One (HC E) where
  one := ⟨1, continuous_const, fun _ => rfl⟩

@[simp] theorem HC.mul_χ (χ ψ : HC E) : (χ * ψ).χ = χ.χ * ψ.χ := rfl
@[simp] theorem HC.inv_χ (χ : HC E) : (χ⁻¹).χ = χ.χ⁻¹ := rfl
@[simp] theorem HC.one_χ : (1 : HC E).χ = 1 := rfl

open scoped Classical in

def locM (P : HeightOneSpectrum (𝓞 E)) : P.adicCompletion E →* AdeleRing (𝓞 E) E where
  toFun x := ((1 : InfiniteAdeleRing E),
    (RestrictedProduct.mulSingle (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletionIntegers E) P x :
      FiniteAdeleRing (𝓞 E) E))
  map_one' := by
    show ((1 : InfiniteAdeleRing E), _) = ((1 : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E))
    rw [RestrictedProduct.mulSingle_one]
    rfl
  map_mul' x y := by
    show ((1 : InfiniteAdeleRing E), _) = ((1 : InfiniteAdeleRing E) * 1, _ * _)
    rw [RestrictedProduct.mulSingle_mul, mul_one]
    rfl

def HC.At (χ : HC E) (P : HeightOneSpectrum (𝓞 E)) (α : ℂ) : Prop :=
  (∀ u : (P.adicCompletion E)ˣ, Valued.v (u : P.adicCompletion E) = 1 → χ.χ (Units.map (locM P) u) = 1) ∧
    ∀ ϖ : (P.adicCompletion E)ˣ, Valued.v (ϖ : P.adicCompletion E) = WithZero.exp (-1 : ℤ) →
      ((χ.χ (Units.map (locM P) ϖ) : ℂˣ) : ℂ) = α

theorem HC.At.mul {χ ψ : HC E} {P : HeightOneSpectrum (𝓞 E)} {a b : ℂ} (h : χ.At P a) (h' : ψ.At P b) :
    (χ * ψ).At P (a * b) := by
  refine ⟨fun u hu => ?_, fun ϖ hϖ => ?_⟩
  · simp [h.1 u hu, h'.1 u hu]
  · simp [← h.2 ϖ hϖ, ← h'.2 ϖ hϖ]

theorem HC.At.inv {χ : HC E} {P : HeightOneSpectrum (𝓞 E)} {a : ℂ} (h : χ.At P a) : (χ⁻¹).At P a⁻¹ := by
  refine ⟨fun u hu => ?_, fun ϖ hϖ => ?_⟩
  · simp [h.1 u hu]
  · simp [← h.2 ϖ hϖ]

theorem exists_unif (P : HeightOneSpectrum (𝓞 E)) :
    ∃ ϖ : (P.adicCompletion E)ˣ, Valued.v (ϖ : P.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hv : Valued.v (π : P.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [P.valuedAdicCompletion_eq_valuation' π, hπ]
  have h0 : (π : P.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  exact ⟨Units.mk0 _ h0, hv⟩

theorem HC.At.unique {χ : HC E} {P : HeightOneSpectrum (𝓞 E)} {a b : ℂ} (ha : χ.At P a) (hb : χ.At P b) : a = b := by
  obtain ⟨ϖ, hϖ⟩ := exists_unif P
  rw [← ha.2 ϖ hϖ, ← hb.2 ϖ hϖ]

open scoped Classical in

def locInf (v : InfinitePlace E) : v.Completion →* AdeleRing (𝓞 E) E where
  toFun x := ((Pi.mulSingle v x : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E))
  map_one' := by
    show ((Pi.mulSingle v (1 : v.Completion) : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E)) =
      ((1 : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E))
    rw [Pi.mulSingle_one]
    rfl
  map_mul' x y := by
    show ((Pi.mulSingle v (x * y) : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E)) =
      ((Pi.mulSingle v x : InfiniteAdeleRing E) * Pi.mulSingle v y, (1 : FiniteAdeleRing (𝓞 E) E) * 1)
    rw [Pi.mulSingle_mul, mul_one]

def HC.Unr (χ : HC E) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ u : (P.adicCompletion E)ˣ, Valued.v (u : P.adicCompletion E) = 1 → χ.χ (Units.map (locM P) u) = 1

def HC.IsUnitArg (χ : HC E) (τ : E →+* ℂ) : Prop :=
  ∀ f : (InfinitePlace.mk τ).Completion →+* ℂ, Continuous f → (∀ x : E, f (x : (InfinitePlace.mk τ).Completion) = τ x) →
    ∀ z : ((InfinitePlace.mk τ).Completion)ˣ,
      ((χ.χ (Units.map (locInf (InfinitePlace.mk τ)) z) : ℂˣ) : ℂ) = f z / (‖f z‖ : ℂ)

def HC.FinOrd (χ : HC E) : Prop := ∃ n : ℕ, 0 < n ∧ ∀ x, χ.χ x ^ n = 1

end hecke

section read

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def Read {A K L : Type} [CommRing A] [CommRing K] [CommRing L] (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω)
    (φ : G E Ω →* Aˣ) (rd : A →+* K) (eL : L →+* K) (embC : L →+* ℂ) (χ : HC E) (w : ℤ) : Prop :=
  ∃ B : Finset (HeightOneSpectrum (𝓞 E)), ∀ P ∉ B, ∃ α : ℂ, χ.At P α ∧ ∃ x : L,
    embC x = α⁻¹ * (Real.sqrt (normV P) : ℂ) ^ w ∧
    ∀ σ : G E Ω, IsFrob (F := E) (pl P) (normV P) σ → rd (φ σ : A) = eL x

abbrev ReadC {A : Type} [CommRing A] (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (φ : G E Ω →* Aˣ)
    (rd : A →+* ℂ) (χ : HC E) (w : ℤ) : Prop :=
  Read pl φ rd (RingHom.id ℂ) (RingHom.id ℂ) χ w

variable (E Ω) in

def cycU (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] : G E Ω →* Oˣ :=
  (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ E Ω l)

def CycFrob (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ P.asIdeal → ∀ σ : G E Ω, IsFrob (F := E) (pl P) (normV P) σ →
    ((cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (normV P : ℤ_[l])

theorem normV_ne_zero (P : HeightOneSpectrum (𝓞 E)) : normV P ≠ 0 := by
  have h : normV P = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [h]
  exact fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)

theorem finite_placesOver (l : ℕ) [Fact l.Prime] :
    {v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

end read

section rcg

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def UnrOut {A : Type} [Group A] (φ : G E Ω →* A) (Q : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := E) A, φ σ = 1

def IsRcgChar (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) {A : Type} [CommGroup A]
    (φ : G E Ω →* A) : Prop :=
  Finite A ∧ (∀ x : A, ∃ n : ℕ, x ^ (l ^ n) = 1) ∧ IsOpen (φ.ker : Set (G E Ω)) ∧ AntiHom c φ ∧ UnrOut φ Q

def rcgKer (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : Subgroup (G E Ω) where
  carrier := {g | ∀ (A : Type) [CommGroup A] (φ : G E Ω →* A), IsRcgChar c l Q φ → φ g = 1}
  one_mem' := fun A _ φ _ => map_one φ
  mul_mem' := fun {a b} ha hb A _ φ h => by rw [map_mul, ha A φ h, hb A φ h, one_mul]
  inv_mem' := fun {a} ha A _ φ h => by rw [map_inv, ha A φ h, inv_one]

theorem mem_rcgKer {c : Ω ≃+* Ω} {l : ℕ} {Q : Set (HeightOneSpectrum (𝓞 E))} {g : G E Ω} :
    g ∈ rcgKer c l Q ↔ ∀ (A : Type) [CommGroup A] (φ : G E Ω →* A), IsRcgChar c l Q φ → φ g = 1 := Iff.rfl

instance rcgKer_normal (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : (rcgKer c l Q).Normal where
  conj_mem g hg h A _ φ hφ := by
    rw [map_mul, map_mul, hg A φ hφ, mul_one, map_inv, mul_inv_cancel]

abbrev RCGGal (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  G E Ω ⧸ rcgKer c l Q

def artGal (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : G E Ω →* RCGGal c l Q :=
  QuotientGroup.mk' _

def RcgOpen (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ [IsAlgClosure E Ω], 0 < l → Q.Finite → (∀ v ∈ Q, ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) →
    IsOpen ((rcgKer c l Q : Subgroup (G E Ω)) : Set (G E Ω))

instance rcgGal_comm (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : CommGroup (RCGGal c l Q) :=
  { (inferInstance : Group (RCGGal c l Q)) with
    mul_comm := fun x y => by
      induction x using QuotientGroup.induction_on with | H a => ?_
      induction y using QuotientGroup.induction_on with | H b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      refine mem_rcgKer.2 fun A _ φ _ => ?_
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm (φ b) (φ a), inv_mul_cancel] }






theorem rcgKer_mono (c : Ω ≃+* Ω) (l : ℕ) {Q Q' : Set (HeightOneSpectrum (𝓞 E))} (h : Q' ⊆ Q) :
    rcgKer c l Q ≤ rcgKer c l Q' := fun _ hg =>
  mem_rcgKer.2 fun A _ φ hφ => (mem_rcgKer.1 hg) A φ
    ⟨hφ.1, hφ.2.1, hφ.2.2.1, hφ.2.2.2.1, fun v hv => hφ.2.2.2.2 v (fun h' => hv (h h'))⟩

def resGal (c : Ω ≃+* Ω) (l : ℕ) {Q Q' : Set (HeightOneSpectrum (𝓞 E))} (h : Q' ⊆ Q) :
    RCGGal c l Q →* RCGGal c l Q' :=
  QuotientGroup.map _ _ (MonoidHom.id _) (fun _ hg => rcgKer_mono c l h hg)




end rcg

end Formalism.L2.NC
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace Formalism.L2.NC

def iotaC (D : D7) (i : D.nd.Loc) : D.nd.O i →+* ℂ :=
  ((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).comp (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))

def complexEmbeddingRestrictedToSubfield (D : D7) : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp D.LL0.val.toRingHom

structure NChiData (D : D7) where

  mu0 : ℕ → HC D.host.E

  etaT : HC D.host.E

  del : D.ntw.Tw → HC D.host.E

  psi : D.nd.Loc → HC D.host.E

  chiI : ∀ s, D.ntw.abelian₂ s → HC D.host.E

  embO : ∀ s, Bool → ↥D.LL0 →+* FractionRing (D.ntw.O s)

def NChiData.firstHeckeCharacter {D : D7} (K : NChiData D) (s : D.ntw.Tw) (j : ℕ) : HC D.host.E :=
  K.mu0 j * K.del s * (K.etaT)⁻¹

def NChiData.lamH {D : D7} (K : NChiData D) (s : D.ntw.Tw) (lam : D.ntw.abelian₂ s) : HC D.host.E :=
  K.mu0 (D.ntw.jL s lam) * K.del s * (K.chiI s lam)⁻¹

def NChiData.chiH {D : D7} (K : NChiData D) (a : D.nd.Loc) : HC D.host.E :=
  K.firstHeckeCharacter (D.ntw.twOf a) (D.nd.j a) * K.psi a

structure NormalizedCharacterCompatibility (D : D7) (K : NChiData D) : Prop where

  psi : ∀ a, ReadC D.nd.plOm.1 (D.ntw.psiL a) (iotaC D a) (K.psi a) 0

  del_fix : ∀ s s', D.ntw.pD s = D.ntw.pD s' → K.del s = K.del s'

  delta : ∀ s, Read D.nd.plOm.1 (D.ntw.delta s) (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s))) (D.ntw.emb0 s)
    (complexEmbeddingRestrictedToSubfield D) (K.del s) 0

  chi1 : ∀ s j (b : Bool), 1 ≤ j → j ≤ D.R.m → Read D.nd.plOm.1 (D.ntw.chi1 s j b) (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)))
    (if b then D.ntw.emb0 s else D.ntw.emb0b s) (complexEmbeddingRestrictedToSubfield D) (K.firstHeckeCharacter s j) (-(D.R.r : ℤ))

  ringSpec_sidedEmbedding_fixedField : ∀ s (b : Bool) (x : ↥D.LL0) (y : D.ntw.O0 s),
    algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)) y = (if b then D.ntw.emb0 s else D.ntw.emb0b s) x →
    K.embO s b x = algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)) (algebraMap (D.ntw.O0 s) (D.ntw.O s) y)

  etaT_unr : ∀ P, K.etaT.Unr P

  etaT_inf : ∀ g : D.R.Psi, K.etaT.IsUnitArg (D.host.emb (g : D.R.GG))

  lamG : ∀ s lam, Read D.nd.plOm.1 (D.ntw.lamG s lam) (algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)))
    (K.embO s (D.ntw.sideL s lam)) (complexEmbeddingRestrictedToSubfield D) (K.lamH s lam) 0


section rcg

variable (D : D7)

theorem art_ker (s : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hQ : ∀ v ∈ Q, v ∉ placesOver D.host.E (D.ntw.l s)) :
    (D.ntw.art s Q).ker = rcgKer D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E))) := by
  ext g
  constructor
  · intro hg
    refine mem_rcgKer.2 fun A _ φ hφ => ?_
    obtain ⟨hfin, hl, hop, han, hun⟩ := hφ
    have := hfin
    obtain ⟨f, hf⟩ := D.ntw.art_univ s Q hQ A hl φ hop han (fun v hv A' hA σ hσ => hun v hv A' hA σ hσ)
    rw [← hf, MonoidHom.comp_apply, (MonoidHom.mem_ker).1 hg, map_one]
  · intro hg
    exact (mem_rcgKer.1 hg) _ (D.ntw.art s Q) ⟨inferInstance, D.ntw.RCG_l s Q, D.ntw.art_cont s Q, D.ntw.art_anti s Q,
      fun v hv A hA σ hσ => D.ntw.art_unr s Q v hv A hA σ hσ⟩

def rcgEquiv (s : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hQ : ∀ v ∈ Q, v ∉ placesOver D.host.E (D.ntw.l s)) :
    D.ntw.RCG s Q ≃* RCGGal D.ntw.cc (D.ntw.l s) (Q : Set (HeightOneSpectrum (𝓞 D.host.E))) :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (D.ntw.art_surj s Q)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (art_ker D s Q hQ))


theorem res_eq (s : D.ntw.Tw) (Q Q' : Finset (HeightOneSpectrum (𝓞 D.host.E))) (h : Q' ⊆ Q)
    (f : D.ntw.RCG s Q →* D.ntw.RCG s Q') (hf : f.comp (D.ntw.art s Q) = D.ntw.art s Q') :
    f = D.ntw.res s Q Q' h := by
  apply MonoidHom.ext
  intro x
  obtain ⟨g, rfl⟩ := D.ntw.art_surj s Q x
  have h1 := congrArg (fun φ => φ g) hf
  simp only [MonoidHom.comp_apply] at h1
  first
  | (have h2 := congrArg (fun φ => φ g) (D.ntw.res_art s Q Q' h)
     simp only [MonoidHom.comp_apply] at h2
     rw [h1, h2])
  | rw [h1, D.ntw.res_art s Q Q' h g]


end rcg







theorem frob_exists (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ σ : G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ :=
  exists_isFrob (D.nd.plOm.2 P)

end Formalism.L2.NC
end
end
