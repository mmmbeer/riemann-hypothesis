import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixLineConjIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicBoundedPolynomials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorIntegralPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderIsHopfOrderNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyPadicBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyBoundedDenominators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitConjOfMinpolyEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugatesAlgebraRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSupportFinitePrimeSet
import Development.AbelianVarietyTheory.Definitions.Divisors.MemShaKernelIffLocallyTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsingletonComplex
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraMapMemMaximalRealSubfieldIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSqrtTotallyNegative
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationComplexConjOfNotSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsUnramifiedAtOfIsSplitAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedAdjoinSqrtOfNotMem
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryTorusNormClassesAtAllPlaces
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementSeparableMinpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPositivityInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveEigenvectorOfSimilitudeUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SylvesterInertiaInvariance
import GroundTheory.AutomorphicForms.Anisotropic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.T2SpaceAfP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingNormFormSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchMu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorMapEigenvalueNormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetAwayP

section
noncomputable section
open NumberField

namespace GlobalTheory.LKTorus.KerOne

variable {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]

def cK (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : L →ₐ[K] L :=
  { c.toRingHom with commutes' := hcK }

@[simp] theorem cK_apply (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) (x : L) :
    cK c hcK x = c x := rfl

def fixOfK (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : Kˣ →* fixU ℚ c where
  toFun a := ⟨Units.map (algebraMap K L : K →* L) a, hcK a⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[simp] theorem fixOfK_apply (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) (a : Kˣ) :
    (((fixOfK c hcK a : fixU ℚ c) : Lˣ) : L) = algebraMap K L a := rfl

variable (K L) in

def ratNormSub : Subgroup Kˣ :=
  (Units.map (algebraMap ℚ K : ℚ →* K)).range ⊔ GlobalTheory.QuadSymbol.globalNorms K L

section Quad

variable [Algebra.IsQuadraticExtension K L]

def cE (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : L ≃ₐ[K] L :=
  AlgEquiv.ofBijective (cK c hcK) (Algebra.IsAlgebraic.algHom_bijective _)

@[simp] theorem cE_apply (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) (x : L) :
    cE c hcK x = c x := rfl

end Quad

end GlobalTheory.LKTorus.KerOne
end
end

section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.LKTorus.KerOneLoc
open GlobalTheory.LKTorus.KerOne

section Basis

variable {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L]

theorem linearIndependent_one_theta (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x)
    (θ : L) (hθ : c θ = -θ) (hθ0 : θ ≠ 0) : LinearIndependent K ![(1 : L), θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
  have h' := congrArg c h
  rw [map_add, map_mul, hcK, hcK, hθ, map_zero] at h'
  have h2 : algebraMap K L (2 * s) = 0 := by rw [map_mul, map_ofNat]; linear_combination h + h'
  have hs : s = 0 := by
    have := (algebraMap K L).injective (h2.trans (map_zero _).symm)
    simpa using this
  subst hs
  rw [map_zero, zero_add] at h
  refine ⟨rfl, ?_⟩
  rcases mul_eq_zero.1 h with h | h
  · exact (algebraMap K L).injective (h.trans (map_zero _).symm)
  · exact absurd h hθ0

end Basis
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc
open GlobalTheory.LKTorus.KerOne

section NormFormula

variable {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L]

def sigmaA (A : Type) [CommRing A] [Algebra K A] (c : L →ₐ[ℚ] L)
    (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : A ⊗[K] L →ₐ[A] A ⊗[K] L :=
  Algebra.TensorProduct.map (AlgHom.id A A) (cK c hcK)

@[simp] theorem sigmaA_tmul (A : Type) [CommRing A] [Algebra K A] (c : L →ₐ[ℚ] L)
    (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) (s : A) (y : L) :
    sigmaA A c hcK (s ⊗ₜ y) = s ⊗ₜ c y := rfl

end NormFormula
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc

section Places

abbrev vP (p : ℕ) [hp : Fact p.Prime] : HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp.out⟩

variable {K : Type} [Field K] [NumberField K]

end Places
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc
open GroundTheory.Global.SemiLocal

section Decomp

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

variable {K : Type} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]

def iotaW (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (vP p).asIdeal] :
    ℚ_[p] →+* w.adicCompletion K :=
  (algebraMap ((vP p).adicCompletion ℚ) (w.adicCompletion K)).comp
    ((Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, hp.out⟩).toRingEquiv.toRingHom)

def phiW (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (vP p).asIdeal] :
    ℚ_[p] ⊗[ℚ] K →ₐ[ℚ] w.adicCompletion K :=
  Algebra.TensorProduct.lift (iotaW p w).toRatAlgHom (algebraMap K (w.adicCompletion K)).toRatAlgHom
    (fun _ _ => Commute.all _ _)

@[simp] theorem phiW_tmul (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (vP p).asIdeal]
    (s : ℚ_[p]) (x : K) : phiW p w (s ⊗ₜ x) = iotaW p w s * algebraMap K (w.adicCompletion K) x := by
  simp [phiW]

end Decomp
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc
open GlobalTheory.LKTorus.KerOne GroundTheory.Global.SemiLocal

section Main

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L]

end Main
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc
open GlobalTheory.LKTorus.KerOne GroundTheory.Global.SemiLocal

section Forward

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L]

variable (K) in

def psiW (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (vP p).asIdeal] :
    ℚ_[p] ⊗[ℚ] L →ₐ[ℚ] w.adicCompletion K ⊗[K] L :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : w.adicCompletion K →ₐ[w.adicCompletion K]
      w.adicCompletion K ⊗[K] L).toRingHom.comp (iotaW p w)).toRatAlgHom)
    ((Algebra.TensorProduct.includeRight : L →ₐ[K] w.adicCompletion K ⊗[K] L).toRingHom.toRatAlgHom)
    (fun _ _ => Commute.all _ _)

end Forward
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc
open GlobalTheory.LKTorus.KerOne GroundTheory.Global.SemiLocal

section Backward

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L]

end Backward
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc

end GlobalTheory.LKTorus.KerOneLoc
end
end

section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} {β : G.Cˣ} {x : (AfP p ⊗[ℚ] G.C)ˣ}
  {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t} {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)}

theorem posV_val_ne_zero (z : PosV G v β) : z.1 ≠ 0 := by
  intro h
  have hz := z.2
  rw [h] at hz
  simp at hz

theorem fixL_smul_vec_iff (y : grp G β) (z : Fin G.n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    FixL G v β y (c • z) ↔ FixL G v β y z := by
  unfold FixL
  simp only [Matrix.mulVec_smul]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [smul_comm e c z] at he
    exact smul_right_injective _ hc he
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [he, smul_comm]⟩

variable (G v β x t hx Kf K')

def orbOfDat (d : Dat G v β) : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
  Quotient.mk'' (LeftCosets.mk _ _ d.1, (Projectivization.mk ℂ d.2.1 (posV_val_ne_zero d.2) : PLv G v β))

theorem orbOfDat_eq_of_same {a b : Dat G v β} (h : Same G v β x t hx Kf K' a b) :
    orbOfDat G v β x t hx Kf K' a = orbOfDat G v β x t hx Kf K' b := by
  obtain ⟨g, k, c, hk1, hk2, hc, h1, h2⟩ := h
  symm
  apply Quotient.sound
  refine ⟨g, Prod.ext ?_ ?_⟩
  · change g • LeftCosets.mk ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1 = LeftCosets.mk _ _ b.1
    rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk, h1, MonoidHom.prod_apply, inv_mul_cancel_left]
    exact Subgroup.mem_prod.2 ⟨hk1, hk2⟩
  · change Projectivization.map (Matrix.toLin' (toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ))
      (toV_injective G v β g) (Projectivization.mk ℂ a.2.1 (posV_val_ne_zero a.2)) =
      Projectivization.mk ℂ b.2.1 (posV_val_ne_zero b.2)
    rw [Projectivization.map_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨c⁻¹, ?_⟩
    rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul, Matrix.toLin'_apply]

def DatWt (f : G.GAf → ℂ) (f' : Gr G 1 → ℂ) (d : Dat G v β) : Prop :=
  ∃ y : grp G β, FixL G v β y d.2.1 ∧
    f (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * f' (d.1.2⁻¹ * toP1 G β y * d.1.2) ≠ 0

theorem datWt_iff_of_same {f : G.GAf → ℂ} {f' : Gr G 1 → ℂ} (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g)
    (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) {a b : Dat G v β} (h : Same G v β x t hx Kf K' a b) :
    DatWt G v β x t hx f f' a ↔ DatWt G v β x t hx f f' b := by
  obtain ⟨g, k, c, hk1, hk2, hc, h1, h2⟩ := h
  have e1 : ∀ y : grp G β, b.1.1⁻¹ * toAfF G β x t hx (g * y * g⁻¹) * b.1.1 =
      k.1⁻¹ * (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * k.1 := by
    intro y; rw [h1]; simp only [Prod.fst_mul, map_mul, map_inv]; group
  have e2 : ∀ y : grp G β, b.1.2⁻¹ * toP1 G β (g * y * g⁻¹) * b.1.2 =
      k.2⁻¹ * (a.1.2⁻¹ * toP1 G β y * a.1.2) * k.2 := by
    intro y; rw [h1]; simp only [Prod.snd_mul, map_mul, map_inv]; group
  have efix : ∀ y : grp G β, FixL G v β (g * y * g⁻¹) b.2.1 ↔ FixL G v β y a.2.1 := by
    intro y
    rw [h2, fixL_smul_vec_iff _ _ hc]
    exact (fixL_conj_iff p G v β y g a.2.1).symm
  constructor
  · rintro ⟨y, hy, hne⟩
    refine ⟨g * y * g⁻¹, (efix y).2 hy, ?_⟩
    rwa [e1, e2, hf _ hk1, hf' _ hk2]
  · rintro ⟨y', hy', hne⟩
    obtain ⟨y, rfl⟩ : ∃ y, y' = g * y * g⁻¹ := ⟨g⁻¹ * y' * g, by group⟩
    refine ⟨y, (efix y).1 hy', ?_⟩
    rwa [e1, e2, hf _ hk1, hf' _ hk2] at hne

end GlobalTheory.CxUnfold
end
end

section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

theorem finite_orbits_of_finite_pts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), Set.Finite {q : Pts G v β x t hx Kf K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0} → {o : MulAction.orbitRel.Quotient (grp G β) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') | ∃ y, GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y ≠ 0}.Finite := by
  intro p _ G v wt Kf f hfi K' f' hfi' β x t hx hT
  let F : Pts G v β x t hx Kf K' → MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
    Quot.lift (orbOfDat G v β x t hx Kf K') (fun a b h => orbOfDat_eq_of_same G v β x t hx _ _ h)
  let PL : Pts G v β x t hx Kf K' → Prop :=
    Quot.lift (DatWt G v β x t hx f f') (fun a b h => propext (datWt_iff_of_same G v β x t hx _ _ hfi hfi' h))
  refine (hT.image F).subset ?_
  rintro o ⟨y, hy⟩
  unfold cxF at hy
  split_ifs at hy with hc
  on_goal 2 => exact absurd rfl hy
  let d : Dat G v β := (LeftCosets.rep _ _ (Quotient.out o).1,
    ⟨Projectivization.rep ((Quotient.out o).2 : Projectivization ℂ (Fin G.n → ℂ)), hc.1⟩)
  have hd : DatWt G v β x t hx f f' d := ⟨y, hc.2, left_ne_zero_of_mul hy⟩
  refine ⟨Quot.mk _ d, ?_, ?_⟩
  · have e : PL (Quot.mk _ (Quot.out (Quot.mk (Same G v β x t hx Kf K') d))) = PL (Quot.mk _ d) :=
      congrArg PL (Quot.out_eq _)
    exact (e : DatWt G v β x t hx f f' _ = DatWt G v β x t hx f f' d).mpr hd
  · show orbOfDat G v β x t hx Kf K' d = o
    simp only [orbOfDat, d, LeftCosets.mk_rep]
    convert Quotient.out_eq' o using 2
    exact Prod.ext rfl (Projectivization.mk_rep _)

end GlobalTheory.CxUnfold
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_weightedPairOrbits_of_finite_weightedFixedPoints : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), Set.Finite {q : Pts G v β x t hx Kf K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0} → {o : MulAction.orbitRel.Quotient (grp G β) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') | ∃ y, GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y ≠ 0}.Finite := by
  first | (exact @GlobalTheory.CxUnfold.finite_orbits_of_finite_pts) | (exact GlobalTheory.CxUnfold.finite_orbits_of_finite_pts) | (intros; apply GlobalTheory.CxUnfold.finite_orbits_of_finite_pts <;> assumption)
end
