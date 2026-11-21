import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ArchimedeanCocycleCharacter
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicNormWeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValueBelow
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClassSumCompare

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
open scoped TensorProduct nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem tmul_eq (a : AdF E) (e : E) :
    (show AdE E from a ⊗ₜ[maximalRealSubfield E] e) = inclF E a * diagE E e := by
  show a ⊗ₜ[maximalRealSubfield E] e = (a ⊗ₜ[maximalRealSubfield E] (1 : E)) * ((1 : AdF E) ⊗ₜ[maximalRealSubfield E] e)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem incl_mem {a : AdF E} (ha : ∀ v : Plc E, a v ∈ v.adicCompletionIntegers (maximalRealSubfield E)) :
    inclF E a ∈ intAd E := Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)

theorem diag_int_mem (o : 𝓞 E) : diagE E (o : E) ∈ intAd E := Subring.subset_closure (Or.inr ⟨o, rfl⟩)

theorem mem_hat_of_mem {x : AdE E} (hx : x ∈ intAd E) :
    (show GlobalTheory.AdLat.RA (maximalRealSubfield E) E from x) ∈
      GlobalTheory.AdLat.hat1 (maximalRealSubfield E) ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  have h1 : (1 : E) ∈ ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := FractionalIdeal.one_mem_one _
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, ha, rfl⟩ | ⟨o, rfl⟩
    · exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral _ ha h1
    · exact GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
  | zero => exact zero_mem _
  | one => exact GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet _ h1
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy =>
    refine GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem _ (fun a ha b hb => ?_) hx hy
    have := FractionalIdeal.mul_mem_mul ha hb
    rwa [mul_one] at this

theorem diag_mem_iff (x : E) : diagE E x ∈ intAd E ↔ ∃ o : 𝓞 E, (o : E) = x := by
  refine ⟨fun h => ?_, ?_⟩
  · exact (FractionalIdeal.mem_one_iff _).1
      ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff (maximalRealSubfield E) 1 x).1 (mem_hat_of_mem h))
  · rintro ⟨o, rfl⟩; exact diag_int_mem o

theorem star_diag (x : E) : star (diagE E x) = diagE E (IsCMField.complexConj E x) := rfl

theorem star_incl (a : AdF E) : star (inclF E a) = inclF E a := by
  show adConj E (a ⊗ₜ 1) = a ⊗ₜ 1
  simp [adConj]

theorem conj_int (a : 𝓞 E) : ∃ b : 𝓞 E, (b : E) = IsCMField.complexConj E (a : E) :=
  ⟨RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv a, rfl⟩

theorem star_mem {x : AdE E} (hx : x ∈ intAd E) : star x ∈ intAd E := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, ha, rfl⟩ | ⟨o, rfl⟩
    · rw [star_incl]; exact incl_mem ha
    · show star (diagE E o) ∈ _
      rw [star_diag, diag_mem_iff]; exact conj_int o
  | zero => rw [star_zero]; exact zero_mem _
  | one => rw [star_one]; exact one_mem _
  | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
  | neg x _ hx => rw [star_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [star_mul]; exact mul_mem hy hx

theorem exists_nat_mul_int (e : E) : ∃ k : ℕ, 0 < k ∧ ∃ o : 𝓞 E, (o : E) = k * e := by
  obtain ⟨k, hk, h⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
  refine ⟨k.natAbs, Int.natAbs_pos.2 hk, ?_⟩
  have h1 := h e (by simp)
  rcases Int.natAbs_eq k with h2 | h2
  · refine ⟨⟨k • e, h1⟩, ?_⟩
    show k • e = _
    conv_lhs => rw [h2]
    simp
  · refine ⟨⟨-(k • e), h1.neg⟩, ?_⟩
    show -(k • e) = _
    conv_lhs => rw [h2]
    simp

theorem diag_algebraMap (x : maximalRealSubfield E) :
    diagE E (algebraMap _ E x) = inclF E (algebraMap _ (AdF E) x) := by
  show (1 : AdF E) ⊗ₜ[maximalRealSubfield E] (algebraMap _ E x) = (algebraMap _ (AdF E) x) ⊗ₜ[maximalRealSubfield E] (1 : E)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_tmul_int (a : AdF E) (e : E) : ∃ (t : maximalRealSubfield E) (o : 𝓞 E),
    inclF E a * diagE E e = inclF E (algebraMap _ (AdF E) t * a) * diagE E (o : E) := by
  obtain ⟨k, hk, o, ho⟩ := exists_nat_mul_int e
  refine ⟨(k : maximalRealSubfield E)⁻¹, o, ?_⟩
  have hk' : (k : E) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  rw [map_mul, ← diag_algebraMap, ho, mul_comm (diagE E _) (inclF E a), mul_assoc, ← map_mul]
  congr 2
  rw [map_inv₀, map_natCast]
  field_simp

theorem approx (m : ℕ) (hm : 0 < m) (x : AdE E) : ∃ e : E, ∃ u ∈ intAd E, x = diagE E e + (m : AdE E) * u := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by show (0 : AdE E) = _; simp⟩
  | tmul a e =>
    obtain ⟨t, o, h⟩ := exists_tmul_int a e
    obtain ⟨x, a', ha', h'⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul _ m hm (algebraMap _ (AdF E) t * a)
    refine ⟨algebraMap _ E x * o, inclF E a' * diagE E o, mul_mem (incl_mem ha') (diag_int_mem o), ?_⟩
    refine (tmul_eq a e).trans ?_
    rw [h, h', map_add, map_mul, diag_algebraMap, map_nsmul, nsmul_eq_mul]
    ring
  | add x y hx hy =>
    obtain ⟨e, u, hu, hx⟩ := hx
    obtain ⟨e', u', hu', hy⟩ := hy
    refine ⟨e + e', u + u', add_mem hu hu', ?_⟩
    show (show AdE E from x) + (show AdE E from y) = _
    rw [show (show AdE E from x) = _ from hx, show (show AdE E from y) = _ from hy, map_add]
    ring

end GlobalTheory.ClassSumCompare
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClassSumCompare

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def flip {X K : Type} [Neg X] (φ : X → K) : X → K := fun x => φ (-x)

section Reps

variable {n : ℕ}

end Reps

section Sums

variable {n : ℕ} {ι : Type} [Fintype ι] {T : Type} [AddCommGroup T] [Module c.F T]

variable {Xo c}

def twist (d : DeltaDat Xo c n) (g : Rul d.Xo₂ d.c₂) : DeltaDat Xo c n := { d with cδ := d.cδ * g }

abbrev Tested {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

variable (Xo c)

end Sums

end GlobalTheory.ClassSumCompare
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaDictCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight GlobalTheory.IndefiniteRowSideFullHecke.ArchimedeanCocycleCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Unif

variable {r : ℕ}

def toU {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) : Formalism.L2.Pj.Unf Xo c σ r :=
  @Formalism.L2.Pj.Unf.mk _ _ _ _ _ _ _ Xo c σ r U.Comp U.fin U.X U.un

def ofU {σ : c.F →+* ℂ} (U : Formalism.L2.Pj.Unf Xo c σ r) : Formalism.L2.PjFree.Unf Xo c σ r :=
  @Formalism.L2.PjFree.Unf.mk _ _ _ _ _ _ _ Xo c σ r U.Comp U.fin U.X U.un

theorem isUnf_toU {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) :
    Formalism.L2.Pj.IsUnf (toU U) ↔ Formalism.L2.PjFree.IsUnf U := Iff.rfl

end Unif

def SameVal (f f' : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), evR Xo c f y = evR Xo c f' y

theorem SameVal.refl (f : Rul Xo c) : SameVal f f := fun _ _ _ _ _ => rfl

section Down

variable {n : ℕ}

def FacTie (d : DeltaDat Xo c n) (cξ : Rul Xo c) (cδ' : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y →
      evR d.Xo₂ d.c₂ cδ' y₂ = evR Xo c cξ y * evR d.Xo₂ d.c₂ d.cδ y₂

variable {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
  {ι : Type} [Fintype ι]

end Down

section Act

variable {G0 : Type} [Group G0]

def CentreTie (e : G0 → LevGrp Dw l) : Prop :=
  (∀ z ∈ Subgroup.center G0, e z ∈ Subgroup.center (LevGrp Dw l)) ∧
    ∀ κ ∈ Subgroup.center (LevGrp Dw l), ∃ z ∈ Subgroup.center G0, e z = κ

def ActTie (e : G0 → LevGrp Dw l) (act : G0 → Rul Xo c →ₗ[c.F] Rul Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ z ∈ Subgroup.center G0, ∀ f ∈ sec Xo c a n, ∀ f' : Rul Xo c, IsLevelAct (e z) f f' ↔ SameVal f' (act z f)

end Act

section Row

variable {D : D7} (V : HSp D) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ)
  (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ) (xi : ℝ)
  (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ}
  {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
  {Tup : Type} (d : Tup → DeltaDat Xo c n) {ι : Tup → Type} [∀ t, Fintype (ι t)] (vol : Tup → ℚ)
  (J : Tup → Subgroup (UA E n)) (h : ∀ t, ι t → UA E n) (N : ∀ t, ι t → ℕ) (ep : Tup → UA E n → ℂ)
  (cξ : Tup → Rul Xo c) (φ : Tup → (Fin n → ConjQ Dw l) → c.F) (φδ : ∀ t, (Fin n → LaJ Xo c (d t)) → c.F)
  (dd : (E →+* ℂ) → ℤ) (lam : ∀ t, J t →* c.Fˣ) (thB : Tup → (UA E n → T) → GA D V → ℂ)
  (q₁ : ℕ) (S : Tup → Finset (Plc E))
  {G0 : Type} [Group G0] (e : G0 → LevGrp Dw l) (act : G0 → Rul Xo c →ₗ[c.F] Rul Xo c)
  (cδ' : ∀ t, Rul (d t).Xo₂ (d t).c₂) (w : ∀ t, ι t → (Fin n → LevQ Dw (d t).l₂) → c.F) (κ : ∀ t, ι t → c.F)
  (thA : ∀ t, (ι t → T) → AutQ V → ℂ) (Pl : ∀ t, (ι t → T) → Prop)

structure Ties : Prop where
  centre : CentreTie e
  level : ActTie e act a n
  keeps : ∀ z ∈ Subgroup.center G0, ∀ f ∈ Formalism.L2.PjFree.cusp Xo c U a n, act z f ∈ Formalism.L2.PjFree.cusp Xo c U a n
  factor : ∀ t, FacTie (d t) (cξ t) (cδ' t)
  fourier : ∀ t i q, (d t).eF (w t i q) = fourierSum (d t).c₂ (coverDatum (d t) (φ t) (φδ t)) q
  scalar : ∀ t i, IsScalar (Dw := Dw) c (ep t) (h t i) (κ t i)
  placed : ∀ t x, Pl t x ↔ ∃ f, IsPlaced c dd (lam t) io f ∧ x = fun i => f (h t i)
  lift : ∀ t f, IsPlaced c dd (lam t) io f → ∀ g, thB t f g = thA t (fun i => f (h t i)) (Quotient.mk _ g)

variable {V U σ dict mu xi a io d vol J h N ep cξ φ φδ dd lam thB q₁ S e act cδ' w κ thA Pl}

end Row

section LevelAction

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.LevelActionLaws

attribute [local instance] Over.cartesianMonoidalCategory

variable {G0 : Type} [Group G0] (lev : G0 → Dw.La →ₗ[𝓞 E] Dw.La)

variable (Xo c) in

def levelAct (g : G0) : Rul Xo c →ₗ[c.F] Rul Xo c :=
  actL (K := c.F) (fun S _ _ => FrPt Xo c S)
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G0) (y y' : FrPt Xo c S) =>
      levActR (Xo := Xo) (c := c) (fun g => (lev g, LinearMap.id)) g' y y') g

variable (Xo c) in

def LevelLaws : Prop :=
  ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G0) (y y' : FrPt Xo c S) =>
      levActR (Xo := Xo) (c := c) (fun g => (lev g, LinearMap.id)) g' y y')

end LevelAction

section Meet

variable {D : D7} {V : HSp D} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r} {σ : c.F →+* ℂ}
  {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {xi : ℝ}
  {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
  {T : Type} [AddCommGroup T] [Module c.F T] {io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F}
  {Tup : Type} {d : Tup → DeltaDat Xo c n} {ι : Tup → Type} [∀ t, Fintype (ι t)] {vol : Tup → ℚ}
  {J : Tup → Subgroup (UA E n)} {h : ∀ t, ι t → UA E n} {N : ∀ t, ι t → ℕ} {ep : Tup → UA E n → ℂ}
  {cξ : Tup → Rul Xo c} {φ : Tup → (Fin n → ConjQ Dw l) → c.F} {φδ : ∀ t, (Fin n → LaJ Xo c (d t)) → c.F}
  {dd : (E →+* ℂ) → ℤ} {lam : ∀ t, J t →* c.Fˣ} {thB : Tup → (UA E n → T) → GA D V → ℂ}
  {q₁ : ℕ} {S : Tup → Finset (Plc E)}

theorem placed_ext {ι₀ : Type} {S₀ : Finset (Plc E)} {J₀ : Subgroup (UA E n)} {h₀ : ι₀ → UA E n} {lam₀ : J₀ →* c.Fˣ}
    (hr : IsRepSystem S₀ J₀ h₀) (hio : Function.Injective io) {f f' : UA E n → T}
    (hf : IsPlaced c dd lam₀ io f) (hf' : IsPlaced c dd lam₀ io f') (e : ∀ i, f (h₀ i) = f' (h₀ i)) : f = f' := by
  funext g
  obtain ⟨i, ⟨γ, hγ, k, hk, rfl⟩, -⟩ := hr.2 g
  choose γ₀ hγ₀ using hγ.1
  have e₀ : γ.1 = (Matrix.of γ₀).map (diagE E) := by
    ext a b
    exact (hγ₀ a b).symm
  exact hio ((hf _ γ e₀ (h₀ i) ⟨k, hk⟩).trans (by rw [e i]; exact (hf' _ γ e₀ (h₀ i) ⟨k, hk⟩).symm))

omit [∀ t, Fintype (ι t)] in

theorem exists_lift (hr : ∀ t, IsRepSystem (S t) (J t) (h t)) (hio : Function.Injective io)
    (hinv : ∀ t f, IsPlaced c dd (lam t) io f → ∀ γ ∈ GQ V, ∀ g, thB t f (γ * g) = thB t f g) :
    ∃ thA : ∀ t, (ι t → T) → AutQ V → ℂ, ∀ t f, IsPlaced c dd (lam t) io f →
      ∀ g, thB t f g = thA t (fun i => f (h t i)) (Quotient.mk _ g) := by
  classical
  refine ⟨fun t x q => if hx : ∃ f, IsPlaced c dd (lam t) io f ∧ x = fun i => f (h t i) then thB t hx.choose q.out
    else 0, fun t f hf g => ?_⟩
  have hx : ∃ f', IsPlaced c dd (lam t) io f' ∧ (fun i => f (h t i)) = fun i => f' (h t i) := ⟨f, hf, rfl⟩
  simp only [dif_pos hx]
  rw [← placed_ext (hr t) hio hf hx.choose_spec.1 (congrFun hx.choose_spec.2)]
  have h1 := Quotient.mk_out (s := QuotientGroup.rightRel (GQ V)) g
  rw [QuotientGroup.rightRel_apply] at h1
  have := hinv t f hf _ h1 (Quotient.mk (QuotientGroup.rightRel (GQ V)) g).out
  rwa [inv_mul_cancel_right] at this

variable {G0 : Type} [Group G0] {e : G0 → LevGrp Dw l} {act : G0 → Rul Xo c →ₗ[c.F] Rul Xo c}
  {cδ' : ∀ t, Rul (d t).Xo₂ (d t).c₂} {w : ∀ t, ι t → (Fin n → LevQ Dw (d t).l₂) → c.F} {κ : ∀ t, ι t → c.F}
  {thA : ∀ t, (ι t → T) → AutQ V → ℂ} {Pl : ∀ t, (ι t → T) → Prop}

end Meet

end GlobalTheory.ThetaDictCompare
end
end
