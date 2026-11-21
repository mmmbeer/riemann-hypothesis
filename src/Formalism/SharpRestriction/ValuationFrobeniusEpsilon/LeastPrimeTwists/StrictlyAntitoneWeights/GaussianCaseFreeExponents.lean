import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.AntitoneWeightsLemma.LiteratureFamilyBoundOfMembers

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain Polynomial

namespace Formalism.MainNotions.V.Pf.V3

variable {D : D7} (V : VData D)

theorem l_ne_zero (l : ℕ) [Fact l.Prime] : ((l : ℕ) : V.Ol l) ≠ 0 := by
  intro h
  have h1 : V.jO l ((l : ℕ) : V.Ol l) = 0 := by rw [h, map_zero]
  rw [map_natCast] at h1
  exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h1

instance instDVR (l : ℕ) [Fact l.Prime] : IsDiscreteValuationRing (V.Ol l) := by
  haveI : IsNoetherianRing (V.Ol l) := IsNoetherianRing.of_finite ℤ_[l] (V.Ol l)
  have hf : ¬ IsField (V.Ol l) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, V.Ol_unram l]
    intro h
    exact l_ne_zero V l (Ideal.span_singleton_eq_bot.mp h)
  refine ((IsDiscreteValuationRing.TFAE (V.Ol l) hf).out 0 4).mpr ?_
  rw [V.Ol_unram l]
  exact ⟨⟨_, rfl⟩⟩

def dK (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] : ℕ := (discr K).natAbs

structure FrobAt (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (p : ℕ) where
  v : HeightOneSpectrum (𝓞 K)
  hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal
  A : ValuationSubring QbarQ
  hA : Formalism.ConjugateSelfDual.IsPlaceOver (F := K) A v
  σ : K.fixingSubgroup
  hσ : Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) (IntermediateField.fixingSubgroupEquiv K σ)
  vp : HeightOneSpectrum (𝓞 ℚ)
  hvp : ((p : ℕ) : 𝓞 ℚ) ∈ vp.asIdeal
  h : ℕ
  hq : Formalism.ConjugateSelfDual.normV v = p ^ h
  h_pos : 1 ≤ h
  h_le : h ≤ 2

namespace FrobAt
variable {K : IntermediateField ℚ QbarQ} [FiniteDimensional ℚ K] {p : ℕ} (Fr : FrobAt K p)

def q : ℕ := Formalism.ConjugateSelfDual.normV Fr.v

def φ : K.fixingSubgroup := Fr.σ⁻¹
end FrobAt

def Sig2 (M e : ℕ) : Set (V.spec ℚ 2).Rep :=
  {π | (V.spec ℚ 2).level π M ∧ (V.spec ℚ 2).wt π = fun _ => ![2 * (e : ℤ), 0]}

def IsRiAt {F : Type} [Field F] [NumberField F] [Algebra F QbarQ] {n l : ℕ} [Fact l.Prime] (ι : QbarL l ≃+* ℂ)
    (π : (V.spec F n).Rep) (ρ : Formalism.ConjugateSelfDual.G F QbarQ →* GL (Fin n) (QbarL l)) : Prop :=
  TV.GeoMatch ρ ι.toRingHom ((V.spec F n).hecke π)

def Ram3 (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) (ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l))
    (M : ℕ) : Prop :=
  (∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ V.Iq q → (σ : GQ) ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.FixMu M →
    ρ σ = 1) ∧
  ∃ a : ℕ, ((l - 1) ∣ a ∨ l ∣ M) ∧
    V.Crys l 3 (HcrSub l a (V.Dq l ⊓ K.fixingSubgroup)) (V.plc l)
      (ρ.comp (Subgroup.inclusion (inf_le_left.trans inf_le_right)))

def Ram2 (l : ℕ) [Fact l.Prime] (W : GQ →* GL (Fin 2) (QbarL l)) (M : ℕ) : Prop :=
  (∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : GQ, σ ∈ V.Iq q → σ ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.FixMu M → W σ = 1) ∧
  ∃ (a : ℕ) (K' : IntermediateField ℚ QbarQ), ((l - 1) ∣ a ∨ l ∣ M) ∧ V.Iq l ≤ K'.fixingSubgroup ∧
    V.Crys l 2 (HcrSub l a (V.Dq l ⊓ K'.fixingSubgroup)) (V.plc l)
      (W.comp (HcrSub l a (V.Dq l ⊓ K'.fixingSubgroup)).subtype)

def IsCSDOne {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {n l : ℕ} [Fact l.Prime]
    (ρ : Formalism.ConjugateSelfDual.G K Ω →* GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) : Prop :=
  ∃ s : K ≃+* K, s ≠ RingEquiv.refl K ∧
    ∃ (τ : Ω ≃+* Ω) (hτ : ∀ x : K, τ (algebraMap K _ x) = algebraMap K _ (s x)), (∀ x, τ (τ x) = x) ∧
    ∃ J : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l), J.det ≠ 0 ∧ J.transpose = J ∧ ∀ σ : Formalism.ConjugateSelfDual.G K Ω,
      (ρ σ : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).transpose * J *
        (ρ (Formalism.ConjugateSelfDual.conjGal s τ hτ σ) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) = J

def OrdFixAt {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]
    (ρ : Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) (A : ValuationSubring Ω) (k : Fin n → ℤ) (M : ℕ) : Prop :=
  ∃ g : GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l),
    (∀ σ ∈ A.decompositionSubgroup F,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).BlockTriangular id) ∧
    ∀ σ ∈ Formalism.ConjugateSelfDual.Inertia (F := F) A, (∀ ζ : Ω, ζ ^ M = 1 → σ ζ = ζ) → ∀ i : Fin n,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) i i =
        ((Formalism.ConjugateSelfDual.cyc F Ω l σ : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) ^ (k i)

def OrdFixAbove {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]
    (ρ : Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) (k : Fin n → ℤ) (M : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → ∀ A, Formalism.ConjugateSelfDual.IsPlaceOver A v → OrdFixAt ρ A k M

def Ord3 {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ QbarQ} [FiniteDimensional ℚ K]
    (ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l)) (e M : ℕ) : Prop :=
  l ≠ 2 ∧ Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ) ∧ IsCSDOne (VData.toRecRep ρ) ∧
    OrdFixAbove (VData.toRecRep ρ) ![(e : ℤ), 0, -(e : ℤ)] M


def Sig3G (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (e : ℕ) : Set (V.spec K 3).Rep :=
  {π | π ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.Sig3 V K (3 * condV D) e ∧
    ∃ (l : ℕ) (_ : Fact l.Prime) (ι : QbarL l ≃+* ℂ) (χ : Chi D) (g1 : GQ) (ξ : V.S3 l e χ K g1 →+* QbarL l),
      UnitaryThreeData V l e χ K ∧ IsNormElt V l e χ K g1 ∧ UnitaryThreeFiniteness V l e χ K g1 ∧ V.IsPt3 ξ ∧
      Continuous (V.rho3 ξ) ∧ Ord3 (V.rho3 ξ) e (condV D) ∧
      IsRiAt V ι π (VData.toRecRep (twistRep (V.rho3 ξ) ((epsL l).comp K.fixingSubgroup.subtype)⁻¹)) ∧
      Ram3 V l K (V.rho3 ξ) (condV D)}

def Sig2G (M e : ℕ) : Set (V.spec ℚ 2).Rep :=
  {π | π ∈ Sig2 V M e ∧
    ∃ (l : ℕ) (_ : Fact l.Prime) (ι : QbarL l ≃+* ℂ) (W : GQ →* GL (Fin 2) (QbarL l)),
      Continuous W ∧ IsRiAt V ι π (twistRep W ((epsL l) ^ e)⁻¹) ∧ Ram2 V l W M}

abbrev Lab (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (e : ℕ) : Type :=
  ↥(Sig3G V K e) ⊕ ↥(Sig2G V (condV D * dK K) e)

theorem sig_three_set_finite_over_field (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (M e : ℕ) :
    (Formalism.MainNotions.UnitaryThreeHeightBounds.Sig3 V K M e).Finite := by
  refine ((V.spec K 3).finite M (fun _ => ![(e : ℤ) + 1, 1, 1 - (e : ℤ)])).subset ?_
  rintro π ⟨-, h2, h3⟩
  exact ⟨h2, funext fun τ => funext fun i => h3 τ i⟩

theorem sig_two_set_finite (M e : ℕ) : (Sig2 V M e).Finite := (V.spec ℚ 2).finite M _

instance (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (e : ℕ) : Finite (Lab V K e) :=
  haveI := ((sig_three_set_finite_over_field V K (3 * condV D) e).subset (fun _ h => h.1 : Sig3G V K e ⊆ _)).to_subtype
  haveI := ((sig_two_set_finite V (condV D * dK K) e).subset (fun _ h => h.1 : Sig2G V (condV D * dK K) e ⊆ _)).to_subtype
  inferInstance

instance (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (e : ℕ) : Fintype (Lab V K e) :=
  Fintype.ofFinite _

section Num

variable {K : IntermediateField ℚ QbarQ} [FiniteDimensional ℚ K] {p : ℕ} (e : ℕ) (χ : Chi D) (Fr : FrobAt K p)

def t3 (π : (V.spec K 3).Rep) : ℂ := ((V.spec K 3).hecke π Fr.v).roots.sum / (Fr.q : ℂ)

def t2 (π : (V.spec ℚ 2).Rep) : ℂ :=
  1 + ((Fr.q : ℂ) ^ e)⁻¹ * (((V.spec ℚ 2).hecke π Fr.vp).roots.map (· ^ Fr.h)).sum

def tt : Lab V K e → ℂ := Sum.elim (fun π => t3 V Fr π.1) (fun π => t2 V e Fr π.1)

def zetaP : ℂ := ((V.chiGQ χ (Fr.φ : GQ) : ℂˣ) : ℂ)

def EisC : ℂ := ((Fr.q : ℂ) ^ e)⁻¹ * zetaP V χ Fr + 1 + (Fr.q : ℂ) ^ e * (zetaP V χ Fr)⁻¹

def fac (τ : Lab V K e) : ℂ := (Fr.q : ℂ) ^ e * (tt V e Fr τ - EisC V e χ Fr)

def prodChi : ℂ := ∏ τ : Lab V K e, fac V e χ Fr τ

open Classical in

def NNc : ℂ := ∏ χ'' ∈ Finset.univ.filter (Formalism.MainNotions.UnitaryThreeHeightBounds.ChiConj D χ), prodChi V e χ'' Fr

end Num

section Ring

variable {V}
variable {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}

variable (V l e χ g1) in

def aP [FiniteDimensional ℚ K] {p : ℕ} (Fr : FrobAt K p) : V.S3 l e χ K g1 :=
  ((V.unitaryGaloisRepresentation l e χ K g1 Fr.φ : GL (Fin 3) (V.S3 l e χ K g1)) : Matrix (Fin 3) (Fin 3) (V.S3 l e χ K g1)).trace -
    algebraMap (V.Ol l) (V.S3 l e χ K g1)
      (V.psi l e χ (Fr.φ : GQ) + 1 + V.psi l e χ ((Fr.φ : GQ)⁻¹))

end Ring

open Formalism.MainNotions.GradedPowerSeriesLemmas in

structure Pres (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ) where
  a : ℕ
  wt : Fin a → ℤ
  𝔓 : Ideal (PT (V.Ol l) wt)
  r : ℕ
  s : ℕ
  r' : ℕ
  s' : ℕ
  m : ℕ
  F : Fin (r + 1) → PT (V.Ol l) wt
  G : Fin s → PT (V.Ol l) wt
  E1 : Fin r' → PT (V.Ol l) wt
  E2 : Fin s' → PT (V.Ol l) wt
  Z : Fin m → PT (V.Ol l) wt
  eS : ST 𝔓 F G E1 E2 Z ≃ₐ[V.Ol l] V.S3 l e χ K g1
  eS_gr : ∀ (j : ℤ) (f : PT (V.Ol l) wt), IsHom j f → eS (mkS 𝔓 F G E1 E2 Z f) ∈ V.S3gr l e χ K g1 j
  eS_sur : ∀ (j : ℤ), ∀ x ∈ V.S3gr l e χ K g1 j, ∃ f : PT (V.Ol l) wt, IsHom j f ∧ eS (mkS 𝔓 F G E1 E2 Z f) = x
  eS_pt : ∀ (hl : l ≠ 2) (f : PT (V.Ol l) wt), V.pt3 l e χ K g1 hl (eS (mkS 𝔓 F G E1 E2 Z f)) = cc f

end Formalism.MainNotions.V.Pf.V3
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain Polynomial

namespace Formalism.MainNotions.V.Pf.V3

variable {D : D7} (V : VData D)

def LGUnr3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ π : (V.spec K 3).Rep, V.IsRACSDC K 3 π →
    ∀ ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l), Continuous ρ → V.IsRi π (VData.toRecRep ρ) →
    ∀ M : ℕ, (V.spec K 3).level π M → ∀ v : HeightOneSpectrum (𝓞 K), ((M : ℕ) : 𝓞 K) ∉ v.asIdeal →
    ((l : ℕ) : 𝓞 K) ∉ v.asIdeal → ∀ (A : ValuationSubring QbarQ) (σ : K.fixingSubgroup),
    Formalism.ConjugateSelfDual.IsPlaceOver (F := K) A v →
    Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) (IntermediateField.fixingSubgroupEquiv K σ) →
    ((ρ σ⁻¹ : GL (Fin 3) (QbarL l)) : Matrix (Fin 3) (Fin 3) (QbarL l)).charpoly.map (V.iotaC l).toRingHom =
      (V.spec K 3).hecke π v

def LGUnr2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (W : GQ →* GL (Fin 2) (QbarL l)), Continuous W →
    Formalism.ConjugateSelfDual.Irred W → V.IsRi π W → ∀ M : ℕ, (V.spec ℚ 2).level π M → ∀ v : HeightOneSpectrum (𝓞 ℚ),
    ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → Formalism.ConjugateSelfDual.UnramAt W v ∧
    ∀ (A : ValuationSubring QbarQ) (σ : GQ),
    Formalism.ConjugateSelfDual.IsPlaceOver (F := ℚ) A v → Formalism.ConjugateSelfDual.IsFrob (F := ℚ) A (Formalism.ConjugateSelfDual.normV v) σ →
    ((W σ⁻¹ : GL (Fin 2) (QbarL l)) : Matrix (Fin 2) (Fin 2) (QbarL l)).charpoly.map (V.iotaC l).toRingHom =
      (V.spec ℚ 2).hecke π v

def LocGlobWt2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (W : GQ →* GL (Fin 2) (QbarL l)), Continuous W → ∀ e : ℕ,
    V.IsRi π (twistRep W ((epsL l) ^ e)⁻¹) →
    (∀ τ, V.HT l 2 ⊤ (V.plc l) (onTop W) τ = ({-(e : ℤ), (e : ℤ)} : Multiset ℤ)) →
    (V.spec ℚ 2).wt π = fun _ => ![2 * (e : ℤ), 0]

def RhoDet3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (π : (V.spec K 3).Rep)
    (ρ ρ' : K.fixingSubgroup →* GL (Fin 3) (QbarL l)), Continuous ρ → Continuous ρ' →
    Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ) → Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ') →
    V.IsRi π (VData.toRecRep ρ) → V.IsRi π (VData.toRecRep ρ') → IsIsoRep ρ ρ'

def RhoDet2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (W W' : GQ →* GL (Fin 2) (QbarL l)), Continuous W →
    Continuous W' → Formalism.ConjugateSelfDual.Irred W → Formalism.ConjugateSelfDual.Irred W' → V.IsRi π W → V.IsRi π W' → IsIsoRep W W'

def HeckeInt3 : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (M e : ℕ), 1 ≤ e → ∀ π ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.Sig3 V K M e, ∀ v : HeightOneSpectrum (𝓞 K),
    ((M : ℕ) : 𝓞 K) ∉ v.asIdeal → ∀ z ∈ ((V.spec K 3).hecke π v).roots,
    IsIntegral ℤ ((Formalism.ConjugateSelfDual.normV v : ℂ) ^ (e - 1) * z)

def HeckeInt2 : Prop :=
  ∀ (M e : ℕ), ∀ π ∈ Sig2 V M e, ∀ v : HeightOneSpectrum (𝓞 ℚ), ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
    ∀ z ∈ ((V.spec ℚ 2).hecke π v).roots, IsIntegral ℤ z

def LocGlob2G : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (ι : QbarL l ≃+* ℂ) (W : GQ →* GL (Fin 2) (QbarL l)),
    Continuous W → ∀ j : ℤ, IsRiAt V ι π (twistRep W ((epsL l) ^ j)) → ∀ M : ℕ, 0 < M → Ram2 V l W M →
    (V.spec ℚ 2).level π M

def CAut (F : Type) [Field F] [NumberField F] (n : ℕ) : Prop :=
  ∀ (π : (V.spec F n).Rep) (σ : ℂ ≃+* ℂ), ∃ π' : (V.spec F n).Rep,
    (∀ M : ℕ, (V.spec F n).level π M → ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
      (V.spec F n).hecke π' v = ((V.spec F n).hecke π v).map σ.toRingHom) ∧
    (∀ τ : F →+* ℂ, (V.spec F n).wt π' (σ.toRingHom.comp τ) = (V.spec F n).wt π τ) ∧
    (V.IsRACSDC F n π → V.IsRACSDC F n π')

def ClozelAutR : Prop :=
  (∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    CAut V K 3) ∧ CAut V ℚ 2

structure Inp : Prop where
  lg3Pt : LG.LocGlob3Pt V
  lg2G : LocGlob2G V
  clozelR : ClozelAutR V
  lgUnr3 : LGUnr3 V
  lgUnr2 : LGUnr2 V
  wt2 : LocGlobWt2 V
  det3 : RhoDet3 V
  det2 : RhoDet2 V
  int3 : HeckeInt3 V
  int2 : HeckeInt2 V
  deJong : Formalism.MainNotions.UnitaryThreeHeightBounds.DeJong D V

def LitGeo : Prop :=
  Formalism.MainNotions.UnitaryThreeHeightBounds.lit0 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.lit1 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.lit2 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.lit3 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.lit4 D V ∧
    Formalism.MainNotions.UnitaryThreeHeightBounds.lit5 D V ∧ LG.lit6Pt D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.lit9 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.LitB D V

def Adm0 : Prop :=
  Formalism.MainNotions.UnitaryThreeHeightBounds.adm1 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.adm2 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.adm3 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.ArchimedeanSignatureMatching D V ∧ UnitaryThreeAutomorphy V ∧
    Formalism.MainNotions.UnitaryThreeHeightBounds.adm6 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.adm8 D V

def Giv : Prop := LitGeo V ∧ Adm0 V ∧ Inp V

structure Dat (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ)
    [FiniteDimensional ℚ K] (g1 : GQ) : Prop where
  data : UnitaryThreeData V l e χ K
  norm : IsNormElt V l e χ K g1
  a : UnitaryThreeFiniteness V l e χ K g1
  b : UnitaryThreeIrreduciblePoints V l e χ K g1

abbrev LW (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ) : Prop :=
  LemmaWAt V l e χ K g1

open Formalism.MainNotions.GradedPowerSeriesLemmas in

def StepA : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∃ P : Pres V l e χ K g1,
      DataM P.𝔓 P.F P.G P.E1 P.E2 P.Z ∧ M1 P.𝔓 P.F P.G P.Z P.r' P.s' l ∧ V.Vlen l e χ ≤ VPrime P.𝔓 P.F

open Formalism.MainNotions.GradedPowerSeriesLemmas in

def ThirdModuleCondition : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ P : Pres V l e χ K g1, DataM P.𝔓 P.F P.G P.E1 P.E2 P.Z →
      M3 P.𝔓 P.F P.G P.E1 P.E2 P.Z

open Formalism.MainNotions.GradedPowerSeriesLemmas in

def FourthModuleCondition : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → LW V l e χ K g1 → ∀ P : Pres V l e χ K g1, DataM P.𝔓 P.F P.G P.E1 P.E2 P.Z →
      M4 P.𝔓 P.F P.G P.E1 P.E2 P.Z

open Classical in

def GaussianCaseFreeExponents (C₁ : ℝ) (bN be : ℕ) : Prop :=
  ∀ e ∈ eRange D, ∀ χ : Chi D, ∀ p : ℕ, p.Prime → ¬ p ∣ 30 * condV D →
    ∃ NN : GaussianInt, NN ≠ 0 ∧
      Real.log ‖GaussianInt.toComplex NN‖ ≤
        C₁ * (Formalism.MainNotions.UnitaryThreeHeightBounds.degQ D χ : ℝ) * (condV D : ℝ) ^ bN * (e : ℝ) ^ be * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ p → ∀ K : IntermediateField ℚ QbarQ, [FiniteDimensional ℚ K] →
        UnitaryThreeData V l e χ K → UnitaryCaseGaussian V l e χ K →
        ∑ χ'' ∈ Finset.univ.filter (Formalism.MainNotions.UnitaryThreeHeightBounds.ChiConj D χ), V.Vlen l e χ'' ≤
          2 * (padicValInt l (Zsqrtd.norm NN) : ℕ∞)

def c4 (β cP cD : ℝ) : ℝ := 8 * max (β * cP) 0 + 3 * max cD 0

open Classical in

def StepOrbCard (D : D7) : Prop :=
  ∀ χ : Chi D, (Finset.univ.filter (Formalism.MainNotions.UnitaryThreeHeightBounds.ChiConj D χ)).card ≤ Formalism.MainNotions.UnitaryThreeHeightBounds.degQ D χ

end Formalism.MainNotions.V.Pf.V3
end
end
