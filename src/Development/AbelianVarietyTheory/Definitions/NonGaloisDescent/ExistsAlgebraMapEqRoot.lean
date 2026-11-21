import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanLPowSIff

section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]

namespace Descent

variable {P : PhiMod O K l e a ι} (Δ : Descent P)

theorem act_mem_Man (g : TameGal K l e a) {v : Vec K a ι} (hv : v ∈ P.Man) : Δ.act g v ∈ P.Man :=
  Δ.act_mem_Mext g (A_le_Rpi l e) (rot_R _) hv

omit [NeZero e] in
theorem act_mem_EM (g : TameGal K l e a) {η : ℕ} {v : Vec K a ι} (hv : v ∈ P.EM η) :
    Δ.act g v ∈ P.EM η := by
  rw [mem_divE, ← act_E_pow_smul]
  exact Δ.act_mem_M g _ hv

omit [NeZero e] in
theorem act_EN (g : TameGal K l e a) (v : Vec K a ι) : Δ.act g (P.EN v) = P.EN (Δ.act g v) := by
  rw [PhiMod.EN_apply, act_E_smul, act_conn, PhiMod.EN_apply]

def actPol : Representation K (TameGal K l e a) P.Pol :=
  Δ.act.quotient P.Man fun g _ => Δ.act_mem_Man g

@[simp] theorem actPol_cls (g : TameGal K l e a) (v : Vec K a ι) :
    Δ.actPol g (P.cls v) = P.cls (Δ.act g v) := rfl

theorem actPol_Mon (g : TameGal K l e a) (y : Vec K a ι) :
    Δ.actPol g (P.Mon y) = P.Mon (Δ.act g y) := by
  rw [PhiMod.Mon_apply, actPol_cls, map_sub, act_EN, act_E_smul, act_zeta, PhiMod.Mon_apply]

theorem cls_mem_invariants {v : Vec K a ι} (hv : v ∈ Δ.inv) : P.cls v ∈ Δ.actPol.invariants :=
  fun g => by rw [actPol_cls, hv g]

theorem Mon_mem_invariants {y : Vec K a ι} (hy : y ∈ Δ.inv) : P.Mon y ∈ Δ.actPol.invariants :=
  fun g => by rw [actPol_Mon, hy g]

def invOf {B : Subalgebra O K⟦X⟧} (W : Submodule B (Vec K a ι)) : Submodule O (Vec K a ι) :=
  W.restrictScalars O ⊓ Δ.inv.restrictScalars O

omit [NeZero e] in
theorem mem_invOf {B : Subalgebra O K⟦X⟧} {W : Submodule B (Vec K a ι)} {v : Vec K a ι} :
    v ∈ Δ.invOf W ↔ v ∈ W ∧ ∀ g, Δ.act g v = v := Iff.rfl

abbrev Minv : Submodule O (Vec K a ι) := Δ.invOf P.M

abbrev Y (η : ℕ) : Submodule O (Vec K a ι) := Δ.invOf (P.EM η)

def Y' (η : ℕ) : Submodule O (Vec K a ι) := (Δ.Y η).map ((mulV K a ι (X ^ e)).restrictScalars O)

abbrev Yl (η : ℕ) : Submodule O (Vec K a ι) := Δ.invOf (divE l e η (P.Mext (invL l (A O K))))

omit [NeZero e] in
theorem mem_Y' {η : ℕ} {y : Vec K a ι} : y ∈ Δ.Y' η ↔ ∃ y₀ ∈ Δ.Y η, (X : K⟦X⟧) ^ e • y₀ = y :=
  Iff.rfl

omit [NeZero e] in
theorem Y'_le_Y (η : ℕ) : Δ.Y' η ≤ Δ.Y η := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨(P.EM η).smul_mem (uIn (A O K) ^ e) hy.1,
    fun g => (Δ.act_X_pow_smul g y).trans (congrArg _ (hy.2 g))⟩

omit [NeZero e] in
theorem mem_Yl_iff {η : ℕ} {y : Vec K a ι} : y ∈ Δ.Yl η ↔ ∃ n : ℕ, (l : K) ^ n • y ∈ Δ.Y η := by
  have hl (n : ℕ) (f : K⟦X⟧) : (l : K) ^ n • f = ((l : A O K) : K⟦X⟧) ^ n * f := by
    simp [smul_eq_C_mul]
  constructor
  · rintro ⟨h1, h2⟩
    choose n hn using fun p : ZMod a × ι => mem_tot.1 h1 p.1 p.2
    refine ⟨Finset.univ.sup n, mem_tot.2 fun τ i => ?_, Δ.inv.smul_mem _ h2⟩
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))
    rw [smul_comm, Pi.smul_apply, Pi.smul_apply, hl, hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (l : A O K).2 c) (hn (τ, i))
  · rintro ⟨n, h1, h2⟩
    refine ⟨mem_tot.2 fun τ i => ⟨n, ?_⟩, fun g => ?_⟩
    · have := mem_tot.1 h1 τ i
      rwa [smul_comm, Pi.smul_apply, Pi.smul_apply, hl] at this
    · exact smul_right_injective _ (pow_ne_zero n (l_ne_zero l)) ((map_smul _ _ _).symm.trans (h2 g))

def Z (η : ℕ) : Submodule O P.Pol :=
  ((P.EM η).restrictScalars O).map (P.cls.restrictScalars O) ⊓ Δ.actPol.invariants.restrictScalars O

theorem mem_Z {η : ℕ} {w : P.Pol} :
    w ∈ Δ.Z η ↔ (∃ y ∈ P.EM η, P.cls y = w) ∧ ∀ g, Δ.actPol g w = w := Iff.rfl

def Zl (η : ℕ) : Submodule K P.Pol := P.PolEta η ⊓ Δ.actPol.invariants

theorem mem_Zl_of_mem_Z {η : ℕ} {w : P.Pol} (hw : w ∈ Δ.Z η) : w ∈ Δ.Zl η := by
  obtain ⟨⟨y, hy, rfl⟩, h⟩ := hw
  exact ⟨P.cls_mem_PolEta hy, h⟩

theorem cls_mem_Z {η : ℕ} {y : Vec K a ι} (hy : y ∈ Δ.Y η) : P.cls y ∈ Δ.Z η :=
  ⟨⟨y, hy.1, rfl⟩, Δ.cls_mem_invariants hy.2⟩


def actO : Representation O (TameGal K l e a) (Vec K a ι) where
  toFun g := (Δ.act g).restrictScalars O
  map_one' := LinearMap.ext fun v => by simp
  map_mul' g h := LinearMap.ext fun v => by simp

omit [NeZero e] in
@[simp] theorem actO_apply (g : TameGal K l e a) (v : Vec K a ι) : Δ.actO g v = Δ.act g v := rfl

def actEM (η : ℕ) : Representation O (TameGal K l e a) ((P.EM η).restrictScalars O) :=
  Δ.actO.subrepresentation _ fun g v hv => by
    rw [Submodule.mem_comap, actO_apply]
    exact Δ.act_mem_EM g hv

omit [NeZero e] in
theorem coe_actEM (η : ℕ) (g : TameGal K l e a) (v : (P.EM η).restrictScalars O) :
    (Δ.actEM η g v : Vec K a ι) = Δ.act g v := rfl

def actQuot (η : ℕ) : Representation O (TameGal K l e a)
    ((P.EM η).restrictScalars O ⧸ (P.M.restrictScalars O).submoduleOf ((P.EM η).restrictScalars O)) :=
  (Δ.actEM η).quotient _ fun g v hv => by
    have h : Δ.act g v ∈ P.M := Δ.act_mem_M g _ hv
    rw [← coe_actEM] at h
    exact h

variable (P) in

def quotToPol (η : ℕ) : ((P.EM η).restrictScalars O ⧸
    (P.M.restrictScalars O).submoduleOf ((P.EM η).restrictScalars O)) →ₗ[O] P.Pol :=
  Submodule.liftQ _ (P.cls.restrictScalars O ∘ₗ Submodule.subtype _)
    fun _ hv => P.cls_eq_zero_iff.2 (P.M_le_Man hv)

theorem quotToPol_act (η : ℕ) (g : TameGal K l e a) (w) :
    quotToPol P η (Δ.actQuot η g w) = Δ.actPol g (quotToPol P η w) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rfl

variable [CompleteSpace K]

omit [NeZero a] [TameDescentExponentData K l e a] in
theorem quotToPol_injective (η : ℕ) : Function.Injective (quotToPol P η) :=
  LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _
    fun y hy => P.mem_M_of_mem_Man y.2 (P.cls_eq_zero_iff.1 hy))

theorem map_invariants_actQuot (η : ℕ) :
    (Δ.actQuot η).invariants.map (quotToPol P η) = Δ.Z η := by
  ext w
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, fun g => by rw [← quotToPol_act, hw g]⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact ⟨y, y.2, rfl⟩
  · rintro ⟨⟨y, hy, rfl⟩, h⟩
    exact ⟨Submodule.Quotient.mk ⟨y, hy⟩, fun g => quotToPol_injective η
      ((Δ.quotToPol_act η g _).trans (h g)), rfl⟩

def quotInvEquiv (η : ℕ) : (Δ.actQuot η).invariants ≃ₗ[O] Δ.Z η :=
  (Submodule.equivMapOfInjective _ (quotToPol_injective η) _).trans
    (LinearEquiv.ofEq _ _ (Δ.map_invariants_actQuot η))

end Descent

namespace Descent

variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}

structure Hom (Δ₁ : Descent P) (Δ₂ : Descent Q) extends BK.Hom P Q where
  app_act : ∀ g v, toHom.app (Δ₁.act g v) = Δ₂.act g (toHom.app v)

namespace Hom

variable {Δ₁ : Descent P} {Δ₂ : Descent Q} {Δ₃ : Descent T} (F : Hom Δ₁ Δ₂)

variable (Δ₁) in

def scalar (c : O) : Hom Δ₁ Δ₁ where
  toHom := BK.Hom.scalar P c
  app_act g v := by
    simp only [BK.Hom.app_scalar, algebraMap_smul]
    exact (map_smul (Δ₁.actO g) c v).symm

def comp (G : Hom Δ₂ Δ₃) (F : Hom Δ₁ Δ₂) : Hom Δ₁ Δ₃ where
  toHom := G.toHom.comp F.toHom
  app_act g v := by rw [BK.Hom.app_comp, BK.Hom.app_comp, F.app_act, G.app_act]

omit [NeZero e] in
theorem app_mem_inv {v : Vec K a ι} (hv : v ∈ Δ₁.inv) : F.app v ∈ Δ₂.inv :=
  fun g => by rw [← F.app_act, hv g]

omit [NeZero e] in
theorem app_mem_Minv {v : Vec K a ι} (hv : v ∈ Δ₁.Minv) : F.app v ∈ Δ₂.Minv :=
  ⟨F.app_mem_M hv.1, F.app_mem_inv hv.2⟩

omit [NeZero e] in
theorem app_mem_Y {η : ℕ} {y : Vec K a ι} (hy : y ∈ Δ₁.Y η) : F.app y ∈ Δ₂.Y η :=
  ⟨F.app_mem_EM hy.1, F.app_mem_inv hy.2⟩

omit [NeZero e] in
theorem app_mem_Y' {η : ℕ} {y : Vec K a ι} (hy : y ∈ Δ₁.Y' η) : F.app y ∈ Δ₂.Y' η := by
  obtain ⟨y₀, h₀, rfl⟩ := Δ₁.mem_Y'.1 hy
  exact Δ₂.mem_Y'.2 ⟨_, F.app_mem_Y h₀, (map_smul _ _ _).symm⟩

theorem onPol_act (g : TameGal K l e a) (w : P.Pol) :
    F.onPol (Δ₁.actPol g w) = Δ₂.actPol g (F.onPol w) := by
  obtain ⟨y, rfl⟩ := P.Man.mkQ_surjective w
  rw [actPol_cls, BK.Hom.onPol_cls, BK.Hom.onPol_cls, actPol_cls, F.app_act]



end Hom

variable (Δ : Descent P) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) (hinv : y ∈ Δ.inv)

def plusInl : Hom Δ (Δ.plus hy hinv) where
  toHom := P.plusInl hy
  app_act g v := by rw [P.plusInl_app, P.plusInl_app, plus_act_join, map_zero]

theorem tameDescent_extended_action_extraVector (g : TameGal K l e a) : (Δ.plus hy hinv).act g xVec = xVec := by
  rw [xVec, plus_act_join, map_zero, map_one]

end Descent

omit [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] in

structure IsExactTriple {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
    (F : Hom P Q) (G : Hom Q T) : Prop where
  inj : ∀ v ∈ P.M, F.app v = 0 → v = 0
  exact : ∀ v ∈ Q.M, G.app v = 0 ↔ v ∈ F.imM
  finiteLength : IsFiniteLength (A O K) G.coker

namespace PhiMod

omit [NeZero a] [TameDescentExponentData K l e a]

variable (P : PhiMod O K l e a ι)

omit [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem nabla_mem_MM_of_basis (h : ∀ i, P.nabla (P.phi (bas i)) ∈ P.MM)
    (h' : ∀ i, P.phi (bas i) ∈ P.MM) {m : Vec K a ι} (hm : m ∈ P.MM) : P.nabla m ∈ P.MM := by
  rw [P.eq_sum_phi_bas m, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hc (τ) := P.mem_extc_iff.1 (mem_tot.1 hm τ) i
  rw [nabla_smul_tot]
  exact add_mem (P.smul_tot_mem_ext (fun τ => derivative_mem_S (hc τ)) (h' i))
    (P.smul_tot_mem_ext hc (h i))

theorem EN_mem_Man_of_basis (h : ∀ i, P.EN (bas i) ∈ P.Man) {m : Vec K a ι} (hm : m ∈ P.Man) :
    P.EN m ∈ P.Man := by
  rw [eq_sum_bas m, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hc (τ) : m τ i ∈ Rpi O K l e := mem_tot.1 hm τ i
  rw [EN_apply, conn_smul_tot, smul_add, smul_comm (E K l e) (fun τ => m τ i)]
  exact add_mem (P.smul_mem_Man (E_mem l e _) (P.smul_tot_mem_Mext
    (fun τ => N_mem (derivative_mem_R l (hc τ))) (P.M_le_Man (P.bas_mem_M i))))
    (P.smul_tot_mem_Mext hc (h i))

omit [NormedAlgebra ℚ_[l] K] [NeZero e] [Fact l.Prime] in
theorem smul_mem_ext_of_basis {c : K⟦X⟧} (h : ∀ i, c • bas i ∈ P.L) {B : Subalgebra O K⟦X⟧}
    (hB : A O K ≤ B) {m : Vec K a ι} (hm : m ∈ P.Mext B) : c • m ∈ P.ext B := by
  rw [eq_sum_bas m, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm]
  exact P.smul_tot_mem_ext (fun τ => mem_tot.1 hm τ i) (P.ext_mono hB (h i))

omit [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem smul_mem_Mext_of_basis {c : K⟦X⟧} (h : ∀ i, c • P.phi (bas i) ∈ P.M) {B : Subalgebra O K⟦X⟧}
    (hB : A O K ≤ B) {m : Vec K a ι} (hm : m ∈ P.ext B) : c • m ∈ P.Mext B := by
  rw [P.eq_sum_phi_bas m, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm]
  exact P.smul_tot_mem_Mext (fun τ => P.mem_extc_iff.1 (mem_tot.1 hm τ) i) (P.Mext_mono hB (h i))

variable {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))

omit [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem bas_inl (i : ι) : bas (Sum.inl i) = (P.plusInl hy).app (bas i) := by
  rw [plusInl_app]
  ext τ (j | j) : 2 <;> simp [bas, join, Pi.single_apply]

omit [IsUltrametricDist K] [Fintype ι] in
theorem bas_inr : (bas (Sum.inr ()) : Vec K a (ι ⊕ Unit)) = xVec := by
  ext τ (j | j) : 2 <;> simp [bas, join, xVec]

theorem plus_upper {η : ℕ} (h : ∀ v ∈ P.L, E K l e ^ η • v ∈ P.M) (hη : y ∈ P.EM η) :
    ∀ v ∈ (P.plus hy).L, E K l e ^ η • v ∈ (P.plus hy).M := fun _ =>
  (P.plus hy).smul_mem_Mext_of_basis (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [P.bas_inl hy, ← Hom.app_phi, ← map_smul]
      exact Hom.app_mem_M _ (h _ (P.phi_mem_L (P.bas_mem_M i)))
    · rw [bas_inr, phi_extension_generator_eq_add, smul_add, ← map_smul, ← bas_inr]
      exact add_mem ((P.plus hy).M.smul_mem (EIn l e (A O K) ^ η) ((P.plus hy).bas_mem_M _))
        (Hom.app_mem_M _ hη)) le_rfl

theorem plus_lower {n : ℕ} (h : ∀ v ∈ P.M, E K l e ^ n • v ∈ P.L) (hn : E K l e ^ n • y ∈ P.L) :
    ∀ v ∈ (P.plus hy).M, E K l e ^ n • v ∈ (P.plus hy).L := fun _ =>
  (P.plus hy).smul_mem_ext_of_basis (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [P.bas_inl hy, ← map_smul]
      exact Hom.app_mem_ext _ le_rfl (h _ (P.bas_mem_M i))
    · rw [bas_inr, eq_sub_of_add_eq (P.phi_extension_generator_eq_add hy).symm, smul_sub,
        ← map_smul (P.plusInl hy).app, ← bas_inr]
      exact sub_mem ((P.plus hy).L.smul_mem (EIn l e (A O K) ^ n)
        ((P.plus hy).phi_mem_L ((P.plus hy).bas_mem_M _))) (Hom.app_mem_ext _ le_rfl hn)) le_rfl


end PhiMod

end GlobalTheory.BK
end
end

section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

theorem exists_eq_mul_add_of_isAdicComplete {R : Type} [CommRing R] (t : R)
    [IsAdicComplete (Ideal.span {t}) R] (T : R →+ R) (hT : ∀ x, T (t * x) = t * T x) (w : R) :
    ∃ x, x = t * T x + w := by
  have hS (n : ℕ) (x y : R) : x ≡ y [SMOD (Ideal.span {t} ^ n • ⊤ : Ideal R)] ↔ t ^ n ∣ x - y := by
    simp [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hd (n : ℕ) (x : R) (h : t ^ n ∣ x) : t ^ (n + 1) ∣ t * T x := by
    obtain ⟨y, rfl⟩ := h
    have : T (t ^ n * y) = t ^ n * T y := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', mul_assoc, hT, ih, mul_assoc]
    exact ⟨T y, by rw [this]; ring⟩
  let f : ℕ → R := fun n => (fun x => t * T x + w)^[n] 0
  have hf (n : ℕ) : f (n + 1) = t * T (f n) + w := Function.iterate_succ_apply' _ _ _
  have h1 (n : ℕ) : t ^ n ∣ f (n + 1) - f n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hf (n + 1), hf n, add_sub_add_right_eq_sub, ← mul_sub, ← map_sub, ← hf]
      exact hd _ _ ih
  obtain ⟨x, hx⟩ := IsPrecomplete.prec' (I := Ideal.span {t}) f (fun {m n} hmn => by
    rw [hS]
    induction hmn with
    | refl => simp
    | step h ih =>
      have := dvd_sub ih ((pow_dvd_pow t h).trans (h1 _))
      convert this using 1
      simp)
  refine ⟨x, sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {t}) _ fun n => ?_)⟩
  rw [hS, sub_zero]
  have := dvd_sub (hd n _ ((hS _ _ _).1 (hx n))) ((hS _ _ _).1 (hx (n + 1)))
  refine (pow_dvd_pow t n.le_succ).trans ?_
  convert this using 1
  rw [hf, map_sub]
  ring

theorem pow_mul_factorial_dvd (l k : ℕ) (hl : 0 < l) : l ^ k * k.factorial ∣ (l * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, l * (k + 1) = m + 1 := ⟨l * (k + 1) - 1, by
      have : 0 < l * (k + 1) := by positivity
      omega⟩
    have h : (l * k).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (by nlinarith)
    rw [hm, Nat.factorial_succ m, ← hm, Nat.factorial_succ, pow_succ]
    refine Dvd.dvd.trans (dvd_of_eq ?_) (mul_dvd_mul_left (l * (k + 1)) (ih.trans h))
    ring

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) {a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem exists_mul_frob_E : ∃ c ∈ S O K e, c * frob K l (E K l e) = l := by
  have hl := (Fact.out : l.Prime).pos
  have : NeZero (e * l) := ⟨(Nat.mul_pos (NeZero.pos e) hl).ne'⟩
  have hl0 := l_ne_zero (K := K) l
  let c : K⟦X⟧ := expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) (PowerSeries.mk 1))
  have hc (n : ℕ) : ‖coeff n c‖ * wS K e n ≤ wS K (e * l) n := by
    rw [coeff_expand]
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h
      rw [wS, wS, Nat.mul_div_cancel_left _ (NeZero.pos (e * l)), mul_assoc e l,
        Nat.mul_div_cancel_left _ (NeZero.pos e), coeff_rescale, coeff_mk, Pi.one_apply, mul_one,
        norm_pow, norm_neg, norm_inv, inv_pow, inv_mul_le_iff₀ (pow_pos (norm_pos_iff.2 hl0) k),
        ← norm_pow, ← norm_mul]
      exact_mod_cast norm_natCast_le_of_dvd (K := K) (pow_mul_factorial_dvd l k hl)
    · simpa using wS_nonneg _ _
  refine ⟨c, ⟨fun n => (hc n).trans (wS_le_one _ _), squeeze_zero
    (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) hc (tendsto_wS l (e * l))⟩, ?_⟩
  have h := congrArg (fun f => expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) f))
    (mk_one_mul_one_sub_eq_one K)
  simp only [map_mul, map_sub, map_one, rescale_X, expand_X, expand_C, map_neg] at h
  have h2 : (C (l : K)⁻¹ : K⟦X⟧) * l = 1 := by
    rw [← map_natCast (C : K →+* K⟦X⟧), ← map_mul, inv_mul_cancel₀ hl0, map_one]
  rw [E, map_add, map_pow, frob_X, map_natCast, ← pow_mul, mul_comm l e]
  linear_combination (l : K⟦X⟧) * h - c * X ^ (e * l) * h2

omit [IsUltrametricDist K] in
theorem E_mul_N_Ezpow (j : ℤ) :
    E K l e * N K (Ezpow K l e j) = (j : K⟦X⟧) * N K (E K l e) * Ezpow K l e j := by
  have key (i : ℤ) : N K (Ezpow K l e (i + 1)) =
      Ezpow K l e i * N K (E K l e) + E K l e * N K (Ezpow K l e i) := by
    rw [Ezpow_add, show Ezpow K l e 1 = E K l e from (Ezpow_natCast l e 1).trans (pow_one _),
      Derivation.leibniz]
    rfl
  have h1 (i : ℤ) : Ezpow K l e (i + 1) = Ezpow K l e i * E K l e := by
    rw [Ezpow_add, show Ezpow K l e 1 = E K l e from (Ezpow_natCast l e 1).trans (pow_one _)]
  induction j using Int.induction_on with
  | zero => simp [Ezpow]
  | succ i ih =>
    rw [key, ih, h1]
    push_cast
    ring
  | pred i ih =>
    have h := key (-i - 1)
    have h' := h1 (-i - 1)
    rw [sub_add_cancel] at h h'
    rw [h, h'] at ih
    refine (isUnit_E (K := K) l e).mul_left_cancel ?_
    push_cast at ih ⊢
    linear_combination ih

omit [IsUltrametricDist K] in
theorem map_Ezpow (f : K⟦X⟧ →+* K⟦X⟧) (hf : f (E K l e) = E K l e) (j : ℤ) :
    f (Ezpow K l e j) = Ezpow K l e j := by
  have h : Units.map (f : K⟦X⟧ →* K⟦X⟧) (isUnit_E (K := K) l e).unit = (isUnit_E l e).unit :=
    Units.ext hf
  conv_rhs => rw [Ezpow, ← h, ← map_zpow]
  rfl

omit [IsUltrametricDist K] in
theorem Ezpow_neg_mul (j : ℤ) : Ezpow K l e (-j) * Ezpow K l e j = 1 := by
  rw [← Ezpow_add]
  simp [Ezpow]

variable {l e}

theorem mx_rankOne_eq (j : ZMod a → ℤ) (τ : ZMod a) (i k : Unit) :
    (rankOne O K l e j).mx τ i k = Ezpow K l e (j τ) := by
  have h : Units.map ((invE l e (A O K)).val : invE l e (A O K) →* K⟦X⟧) (Eunit O K l e) =
      (isUnit_E l e).unit := Units.ext rfl
  rw [Ezpow, ← h, ← map_zpow]
  rw [PhiMod.mx, rankOne]
  dsimp only
  generalize Eunit O K l e ^ j τ = u
  simp

theorem mxInv_rankOne_eq (j : ZMod a → ℤ) (τ : ZMod a) (i k : Unit) :
    (rankOne O K l e j).mxInv τ i k = Ezpow K l e (-j τ) := by
  have h := congrFun (congrFun ((rankOne O K l e j).mxInv_mul_mx τ) ()) ()
  rw [Matrix.mul_apply, Fintype.sum_unique, mx_rankOne_eq, Matrix.one_apply_eq,
    ← Ezpow_neg_mul l e (j τ)] at h
  exact mul_right_cancel₀ (Units.ne_zero _) h

theorem phi_bas_rankOne (j : ℤ) : (rankOne O K l e fun _ : ZMod a => j).phi (bas ()) =
    Ezpow K l e j • bas () := by
  ext τ i : 2
  simp [PhiMod.phi_bas, mx_rankOne_eq, bas]

theorem mem_ext_rankOne (j : ℤ) {B : Subalgebra O K⟦X⟧} {v : Vec K a Unit} :
    v ∈ (rankOne O K l e fun _ : ZMod a => j).ext B ↔ ∀ τ, Ezpow K l e (-j) * v τ () ∈ B := by
  simp [PhiMod.ext, mem_tot, PhiMod.mem_extc_iff, mem_vecs, Matrix.mulVec, dotProduct,
    mxInv_rankOne_eq]

variable [CompleteSpace K]

theorem exists_nabla_rankOne (j : ℤ) : ∃ γ ∈ S O K e,
    (rankOne O K l e fun _ : ZMod a => j).nabla (Ezpow K l e j • bas ()) =
      γ • Ezpow K l e j • bas () := by
  set P := rankOne O K l e fun _ : ZMod a => j
  obtain ⟨c, hc, hcE⟩ := exists_mul_frob_E (O := O) (K := K) l e
  obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := Nat.exists_eq_succ_of_ne_zero (Fact.out : l.Prime).ne_zero
  obtain ⟨n, hn⟩ : ∃ n, l * e = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (mul_ne_zero (Fact.out : l.Prime).ne_zero (NeZero.ne e))
  have := isAdicComplete_S O K l e
  obtain ⟨γ, hγ⟩ := exists_eq_mul_add_of_isAdicComplete (l : S O K e)
    { toFun := fun x => uIn _ ^ m * ⟨_, frob_mem_S l x.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp [mul_add]) }
    (fun x => Subtype.ext (by simp [mul_left_comm])) (-((j : S O K e) * (e : S O K e) * uIn (S O K e) ^ n * (⟨c, hc⟩ : S O K e)))
  have hγ' : (γ : K⟦X⟧) = (l : K⟦X⟧) * (X ^ m * frob K l γ) +
      -((j : K⟦X⟧) * (e : K⟦X⟧) * (X : K⟦X⟧) ^ n * c) := by
    simpa using congrArg Subtype.val hγ
  refine ⟨γ, γ.2, smul_right_injective _ (X_ne_zero (R := K)) ?_⟩
  have hq : (l : K⟦X⟧) * frob K l (N K (Ezpow K l e (-j)) * Ezpow K l e j) =
      -((j : K⟦X⟧) * (e : K⟦X⟧) * (X : K⟦X⟧) ^ (n + 1) * c) := by
    have h1 : E K l e * (N K (Ezpow K l e (-j)) * Ezpow K l e j) = -((j : K⟦X⟧) * (e : K⟦X⟧) * (X : K⟦X⟧) ^ e) := by
      rw [← mul_assoc, E_mul_N_Ezpow, mul_assoc, Ezpow_neg_mul, N_E]
      push_cast
      ring
    have h2 := congrArg (frob K l) h1
    simp only [map_mul, map_neg, map_pow, frob_X, map_natCast, map_intCast, ← pow_mul, hn] at h2 ⊢
    rw [← hcE]
    linear_combination c * h2
  have hb : (bas () : Vec K a Unit) = Ezpow K l e (-j) • Ezpow K l e j • bas () := by
    rw [smul_smul, Ezpow_neg_mul, one_smul]
  have hl (v : Vec K a Unit) : (l : K) • v = (l : K⟦X⟧) • v := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hR : Raises (P.lphi * mulV K a Unit (Ezpow K l e (-j))) := fun k v hv =>
    P.raises_lphi k _ ((uPow K a Unit _).smul_mem _ hv)
  change P.conn _ = (X : K⟦X⟧) • (γ : K⟦X⟧) • Ezpow K l e j • bas ()
  rw [← sub_eq_zero, smul_smul X]
  refine hR.eq_zero (σ := (id : Unit → Unit)) Function.surjective_id
    (δ := fun _ => P.conn (Ezpow K l e j • bas ()) - (X * (γ : K⟦X⟧)) • Ezpow K l e j • bas ())
    (fun _ => sub_mem (P.conn_mem_uPow _) (by rw [mul_smul]; exact X_smul_mem_uPow _))
    (fun _ => ?_) ()
  have h3 : Ezpow K l e (-j) • P.conn (Ezpow K l e j • bas ()) =
      P.conn (bas ()) - (N K (Ezpow K l e (-j)) * Ezpow K l e j) • bas () := by
    conv_rhs => rw [hb, P.conn_smul, ← hb, mul_smul, add_sub_cancel_left]
  rw [Module.End.mul_apply, mulV_apply, smul_sub, h3, smul_comm _ (X * (γ : K⟦X⟧)), ← hb, map_sub,
    map_sub, P.lphi_apply, ← P.conn_phi, P.lphi_apply, P.lphi_apply, P.phi_smul, P.phi_smul,
    phi_bas_rankOne, hl, hl, smul_smul (l : K⟦X⟧), smul_smul (l : K⟦X⟧), hq, sub_sub, ← add_smul,
    map_mul, frob_X]
  congr 2
  have hX : (X : K⟦X⟧) ^ l = X ^ (m + 1) := by rw [← hm]
  linear_combination X * hγ' - l * frob K l γ * hX

end GlobalTheory.BK
end
end

section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

structure BKDat (η H : ℕ) extends PhiMod O K l e a ι where

  desc : Descent toPhiMod
  nabla_mem : ∀ m ∈ toPhiMod.MM, toPhiMod.nabla m ∈ toPhiMod.MM
  EN_mem : ∀ m ∈ toPhiMod.M, toPhiMod.EN m ∈ toPhiMod.Man
  lower : ∀ m ∈ toPhiMod.M, E K l e ^ H • m ∈ toPhiMod.L
  upper : ∀ m ∈ toPhiMod.L, E K l e ^ η • m ∈ toPhiMod.M

section RankOne

variable {O K l e a}

omit [NeZero a] [TameDescentExponentData K l e a] in
theorem Ezpow_mem_A {i : ℤ} (hi : 0 ≤ i) : Ezpow K l e i ∈ A O K := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  rw [Ezpow_natCast]
  exact pow_mem (E_mem l e _) n

def rankOneDesc (j : ℤ) (χ : TameGal K l e a →* O) :
    Descent (rankOne O K l e fun _ : ZMod a => j) :=
  Descent.ofMatrix _ (fun g _ => Matrix.of fun _ _ => C (algebraMap O K (χ g)))
    (fun g _ _ _ => by
      rw [Matrix.of_apply, ← algebraMap_eq_C]
      exact Subalgebra.algebraMap_mem _ _)
    (fun _ => by ext1 i k; simp [Subsingleton.elim i k])
    (fun g h τ => by
      ext1 i k
      have := congrFun ((ringAct g).commutes (algebraMap O K (χ h))) τ
      simp only [Matrix.mul_apply, Fintype.sum_unique, Matrix.of_apply, Matrix.map_apply, map_mul]
      exact congrArg _ this.symm)
    fun g τ => by
      ext1 i k
      simp only [Matrix.mul_apply, Fintype.sum_unique, Matrix.of_apply, Matrix.map_apply,
        mx_rankOne_eq, frob_C]
      rw [map_Ezpow l e _ (congrFun (ringAct_E g) τ), mul_comm]

theorem rankOneDesc_act (j : ℤ) (χ : TameGal K l e a →* O) (g : TameGal K l e a)
    (v : Vec K a Unit) (τ : ZMod a) : (rankOneDesc j χ).act g v τ () =
      C (algebraMap O K (χ g)) * rescale (g.root τ) (v (τ - g.shift) ()) := by
  change Descent.matAct g _ v τ () = _
  simp [Descent.matAct_apply, Matrix.mulVec, dotProduct]

variable [CompleteSpace K]

omit [NeZero a] [TameDescentExponentData K l e a] in
theorem exists_EN_bas_rankOne (j : ℤ) : ∃ γ ∈ S O K e,
    (rankOne O K l e fun _ : ZMod a => j).EN (bas ()) =
      (E K l e * γ - (j : K⟦X⟧) * N K (E K l e)) • bas () := by
  obtain ⟨γ, hγ, h⟩ := exists_nabla_rankOne (O := O) (K := K) (l := l) (e := e) (a := a) j
  refine ⟨X * γ, mul_mem HasU.X_mem hγ, smul_right_injective _ (r := Ezpow K l e j)
    (Units.ne_zero _) ?_⟩
  have h1 := congrArg (fun v => E K l e • (X : K⟦X⟧) • v) h
  simp only [← PhiMod.conn_apply, PhiMod.conn_smul, smul_add, smul_smul, E_mul_N_Ezpow] at h1
  simp only [PhiMod.EN_apply, smul_smul]
  rw [mul_comm, eq_sub_of_add_eq' h1, ← sub_smul]
  congr 1
  ring

variable (O K l e a) in

def rankOneDat (η H : ℕ) (j : ℤ) (h₁ : -(η : ℤ) ≤ j) (h₂ : j ≤ H) (χ : TameGal K l e a →* O) :
    BKDat O K l e a Unit η H where
  toPhiMod := rankOne O K l e fun _ => j
  desc := rankOneDesc j χ
  nabla_mem _ := by
    have h (i : Unit) := PhiMod.ext_mono _ (A_le_S l e)
      (PhiMod.phi_mem_L _ ((rankOne O K l e fun _ : ZMod a => j).bas_mem_M i))
    refine PhiMod.nabla_mem_MM_of_basis _ (fun i => ?_) h
    obtain ⟨γ, hγ, h'⟩ := exists_nabla_rankOne (O := O) (K := K) (l := l) (e := e) (a := a) j
    rw [phi_bas_rankOne, h', ← phi_bas_rankOne (O := O)]
    exact Submodule.smul_mem _ (⟨γ, hγ⟩ : S O K e) (h ())
  EN_mem _ hm := PhiMod.EN_mem_Man_of_basis _ (fun i => by
    obtain ⟨γ, hγ, h⟩ := exists_EN_bas_rankOne (O := O) (K := K) (l := l) (e := e) (a := a) j
    rw [h]
    exact PhiMod.smul_mem_Man _ (sub_mem (mul_mem (E_mem l e _) (S_le_R l e hγ))
      (mul_mem (intCast_mem _ j) (N_mem (derivative_mem_R l (E_mem l e _)))))
      (PhiMod.M_le_Man _ (PhiMod.bas_mem_M _ _))) (PhiMod.M_le_Man _ hm)
  lower m hm := (mem_ext_rankOne j).2 fun τ => by
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Ezpow_natCast, ← Ezpow_add]
    exact mul_mem (Ezpow_mem_A (by omega)) (mem_tot.1 hm τ ())
  upper m hm := mem_tot.2 fun τ i => by
    have := mul_mem (Ezpow_mem_A (l := l) (e := e) (i := η + j) (by omega))
      ((mem_ext_rankOne j).1 hm τ)
    rwa [← mul_assoc, ← Ezpow_add, add_neg_cancel_right, Ezpow_natCast] at this

end RankOne

variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}

abbrev BKHom (D : BKDat O K l e a ι η H) (D' : BKDat O K l e a κ η' H') : Type :=
  Descent.Hom D.desc D'.desc

namespace BKDat

variable (D : BKDat O K l e a ι η H)

abbrev Y : Submodule O (Vec K a ι) := D.desc.Y η

abbrev Y' : Submodule O (Vec K a ι) := D.desc.Y' η

abbrev Yl : Submodule O (Vec K a ι) := D.desc.Yl η

abbrev Minv : Submodule O (Vec K a ι) := D.desc.Minv

abbrev Z : Submodule O D.Pol := D.desc.Z η

abbrev Zl : Submodule K D.Pol := D.desc.Zl η

structure IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) : Prop where
  chars_subset : ∀ τ, D.desc.chars τ ⊆ Sig
  jumps_subset : D.jumps ⊆ U

omit [NeZero e] in

theorem exists_conn_eq {m : Vec K a ι} (hm : m ∈ D.MM) : ∃ w ∈ D.MM, D.conn m = (X : K⟦X⟧) • w :=
  ⟨_, D.nabla_mem m hm, rfl⟩

omit [NeZero e] in
theorem conn_mem_MM {m : Vec K a ι} (hm : m ∈ D.MM) : D.conn m ∈ D.MM :=
  D.MM.smul_mem (uIn (S O K e)) (D.nabla_mem m hm)

theorem EN_mem_Man {m : Vec K a ι} (hm : m ∈ D.Man) : D.EN m ∈ D.Man :=
  D.EN_mem_Man_of_basis (fun i => D.EN_mem _ (D.bas_mem_M i)) hm

theorem EN_mem_divE {n : ℕ} {y : Vec K a ι} (hy : y ∈ divE l e n D.Man) :
    D.EN y ∈ divE l e n D.Man := by
  rw [mem_divE, D.E_pow_smul_EN]
  exact sub_mem (D.EN_mem_Man hy) (D.smul_mem_Man
    (mul_mem (natCast_mem _ n) (N_mem (derivative_mem_R l (E_mem l e _)))) hy)

omit [NeZero e] in
theorem conn_bas_mem (i : ι) : D.conn (bas i) ∈ D.Mext (RpiE O K l e) :=
  D.mem_Mext_invE_of_mem_divE (n := 1) (by rw [pow_one]; exact D.EN_mem _ (D.bas_mem_M i))

theorem hatTot_conn [CompleteSpace K] {v : Vec K a ι} (hv : v ∈ D.Mext (RpiE O K l e)) :
    D.hatTot (D.conn v) = D.connHat (D.hatTot v) := D.toPhiMod.hatTot_conn D.conn_bas_mem hv

omit [NeZero e] in

theorem smul_mem_Mext {B : Subalgebra O K⟦X⟧} (hB : A O K ≤ B) {m : Vec K a ι} (hm : m ∈ D.ext B) :
    E K l e ^ η • m ∈ D.Mext B :=
  D.smul_mem_Mext_of_basis (fun i => D.upper _ (D.phi_mem_L (D.bas_mem_M i))) hB hm

def Lc : Module.End K D.Pol := D.Man.mapQ D.Man D.EN fun _ => D.EN_mem_Man

@[simp] theorem Lc_cls (v : Vec K a ι) : D.Lc (D.cls v) = D.cls (D.EN v) := rfl

theorem Lc_mem_PolEta {n : ℕ} {w : D.Pol} (hw : w ∈ D.PolEta n) : D.Lc w ∈ D.PolEta n := by
  obtain ⟨y, hy, rfl⟩ := hw
  exact ⟨_, D.EN_mem_divE hy, rfl⟩

theorem actPol_Lc (g : TameGal K l e a) (w : D.Pol) :
    D.desc.actPol g (D.Lc w) = D.Lc (D.desc.actPol g w) := by
  obtain ⟨y, rfl⟩ := D.Man.mkQ_surjective w
  rw [Lc_cls, Descent.actPol_cls, Descent.actPol_cls, Lc_cls, Descent.act_EN]

theorem Lc_mem_Zl {w : D.Pol} (hw : w ∈ D.Zl) : D.Lc w ∈ D.Zl :=
  ⟨D.Lc_mem_PolEta hw.1, fun g => by rw [actPol_Lc, hw.2 g]⟩

def LcZ : Module.End K D.Zl := D.Lc.restrict fun _ => D.Lc_mem_Zl

@[simp] theorem coe_LcZ (w : D.Zl) : (D.LcZ w : D.Pol) = D.Lc w := rfl

theorem Mon_eq (y : Vec K a ι) : D.Mon y = D.Lc (D.cls y) - D.cls (E K l e • D.zeta y) := by
  rw [PhiMod.Mon_apply, map_sub, Lc_cls]

theorem Mon_add_phi_sub (y : Vec K a ι) {m : Vec K a ι} (hm : m ∈ D.Man) :
    D.Mon (y + (D.phi m - m)) = D.Mon y := by
  rw [map_add, PhiMod.Mon_phi_sub, D.cls_eq_zero_iff.2 (D.EN_mem_Man hm), neg_zero, add_zero]


theorem _root_.GlobalTheory.BK.BKHom.onPol_Lc {D : BKDat O K l e a ι η H} {D' : BKDat O K l e a κ η' H'}
    (F : BKHom D D') (w : D.Pol) : F.onPol (D.Lc w) = D'.Lc (F.onPol w) := by
  obtain ⟨y, rfl⟩ := D.Man.mkQ_surjective w
  rw [Lc_cls, Hom.onPol_cls, Hom.onPol_cls, Lc_cls, Hom.app_EN]

variable {D} {y : Vec K a ι}

omit [NeZero e] in
theorem mem_invE_of_mem_Y (hy : y ∈ D.Y) : y ∈ D.Mext (invE l e (A O K)) :=
  D.mem_Mext_invE_of_mem_divE hy.1

abbrev plusMod (hy : y ∈ D.Y) : PhiMod O K l e a (ι ⊕ Unit) := D.plus (mem_invE_of_mem_Y hy)

abbrev plusDesc (hy : y ∈ D.Y) : Descent (plusMod hy) := D.desc.plus (mem_invE_of_mem_Y hy) hy.2

omit [NeZero e] in

theorem plusMod_upper (hy : y ∈ D.Y) : ∀ v ∈ (plusMod hy).L, E K l e ^ η • v ∈ (plusMod hy).M :=
  D.plus_upper _ D.upper hy.1

omit [NeZero e] in

theorem plusMod_lower (hy : y ∈ D.Y) :
    ∀ v ∈ (plusMod hy).M, E K l e ^ (H + η) • v ∈ (plusMod hy).L :=
  D.plus_lower _ (fun v hv => by
    rw [pow_add, mul_smul]
    exact D.lower _ (D.M.smul_mem (EIn l e (A O K) ^ η) hv)) (by
    rw [pow_add, mul_smul]
    exact D.lower _ hy.1)

def plusDat (hy : y ∈ D.Y) (hMon : D.Mon y = 0) (hz : ∃ w ∈ D.MM, D.zeta y = (X : K⟦X⟧) • w)
    (hH : E K l e ^ H • y ∈ D.L) : BKDat O K l e a (ι ⊕ Unit) η H where
  toPhiMod := plusMod hy
  desc := plusDesc hy
  nabla_mem _ := PhiMod.nabla_mem_MM_of_basis _ (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [D.bas_inl (mem_invE_of_mem_Y hy), ← Hom.app_phi, ← Hom.app_nabla]
      exact Hom.app_mem_ext _ (A_le_S l e) (D.nabla_mem _
        (D.ext_mono (A_le_S l e) (D.phi_mem_L (D.bas_mem_M i))))
    · obtain ⟨w, hw, h⟩ := hz
      have h1 := D.conn_phi_extension_generator_eq_zeta (mem_invE_of_mem_Y hy)
      rw [h, map_smul, PhiMod.conn_apply] at h1
      rw [PhiMod.bas_inr, smul_right_injective _ X_ne_zero h1]
      exact Hom.app_mem_ext _ (A_le_S l e) hw)
    fun i => PhiMod.ext_mono _ (A_le_S l e) (PhiMod.phi_mem_L _ (PhiMod.bas_mem_M _ i))
  EN_mem _ hm := PhiMod.EN_mem_Man_of_basis _ (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [D.bas_inl (mem_invE_of_mem_Y hy), ← Hom.app_EN]
      exact Hom.app_mem_Mext _ (A_le_Rpi l e) (D.EN_mem _ (D.bas_mem_M i))
    · rw [PhiMod.bas_inr]
      exact (D.Mon_eq_zero_iff _).1 hMon) (PhiMod.M_le_Man _ hm)
  lower := D.plus_lower _ D.lower hH
  upper := plusMod_upper hy

end BKDat

namespace Descent

variable {P : PhiMod O K l e a ι} (Δ : Descent P)

def avg : Module.End K (Vec K a ι) :=
  letI := Fintype.ofFinite (TameGal K l e a)
  ((Nat.card (TameGal K l e a) : K)⁻¹) • ∑ g, Δ.act g

omit [IsUltrametricDist K] in
theorem norm_card : ‖(Nat.card (TameGal K l e a) : K)‖ = 1 := by
  rw [norm_natCast_eq l, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 TameGal.not_dvd_card

theorem avg_mem_inv (v : Vec K a ι) : Δ.avg v ∈ Δ.inv := fun g => by
  let _ := Fintype.ofFinite (TameGal K l e a)
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    ← Module.End.mul_apply, ← map_mul]
  exact congrArg _ (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun _ => rfl)

theorem map_avg {V : Type} [AddCommGroup V] [Module K V] (f : Vec K a ι →ₗ[K] V) {v : Vec K a ι}
    (h : ∀ g, f (Δ.act g v) = f v) : f (Δ.avg v) = f v := by
  let _ := Fintype.ofFinite (TameGal K l e a)
  have h0 : (Nat.card (TameGal K l e a) : K) ≠ 0 := norm_ne_zero_iff.1 (by rw [norm_card]; simp)
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, h, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, inv_smul_smul₀ h0]


theorem avg_mem (W : Submodule O (Vec K a ι)) {v : Vec K a ι} (h : ∀ g, Δ.act g v ∈ W) :
    Δ.avg v ∈ W := by
  obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O) ((Nat.card (TameGal K l e a) : K)⁻¹)).2
    (by rw [norm_inv, norm_card, inv_one])
  rw [avg, LinearMap.smul_apply, LinearMap.sum_apply, ← hc, algebraMap_smul]
  exact W.smul_mem c (W.sum_mem fun g _ => h g)

theorem map_Y (η : ℕ) : (Δ.Y η).map (P.cls.restrictScalars O) = Δ.Z η := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact Δ.cls_mem_Z hy
  · obtain ⟨⟨y, hy, rfl⟩, h⟩ := Δ.mem_Z.1 hw
    exact ⟨Δ.avg y, ⟨Δ.avg_mem _ fun g => Δ.act_mem_EM g hy, Δ.avg_mem_inv y⟩, Δ.map_avg P.cls h⟩

end Descent

section Examples

omit [NeZero a] [TameDescentExponentData K l e a]

theorem Ezpow_mem_invL_A_iff {i : ℤ} : Ezpow K l e i ∈ invL l (A O K) ↔ 0 ≤ i := by
  refine ⟨fun h => not_lt.1 fun hi => ?_, fun h => le_away (A O K) _ (Ezpow_mem_A h)⟩
  have h0 : Ezpow K l e (-1 - i) ∈ invL l (A O K) := le_away _ _ (Ezpow_mem_A (by omega))
  have h1 := mul_mem h0 h
  rw [← Ezpow_add, sub_add_cancel] at h1
  have h2 : E K l e * Ezpow K l e (-1) = 1 := by simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
  have h3 : Ezpow K l e (-1) = 0 := eq_zero_of_E_mul l e (invL_A_le_Rpi l e h1) fun n => by
    rw [h2, coeff_one, if_neg (by have := NeZero.pos e; omega)]
  exact Units.ne_zero _ h3

theorem mem_shiftE_of_le {P : PhiMod O K l e a ι} {i k : ℤ} (h : i ≤ k) {v : Vec K a ι}
    (hv : v ∈ shiftE l e k (P.Mext (invL l (A O K)))) :
    v ∈ shiftE l e i (P.Mext (invL l (A O K))) := by
  have := (P.Mext (invL l (A O K))).smul_mem
    ⟨_, (Ezpow_mem_invL_A_iff (e := e)).2 (sub_nonneg.2 h)⟩ hv
  rwa [Subalgebra.smul_def, smul_smul, ← Ezpow_add, show k - i + -k = -i by ring] at this

theorem filL_rankOne (j i : ℤ) : (rankOne O K l e fun _ : ZMod a => j).filL i =
    shiftE l e (if i ≤ j then j else j + 1)
      ((rankOne O K l e fun _ : ZMod a => j).Mext (invL l (A O K))) := by
  set P := rankOne O K l e fun _ : ZMod a => j
  have h0 : P.ext (invL l (A O K)) = shiftE l e j (P.Mext (invL l (A O K))) := by
    ext v
    exact (mem_ext_rankOne j).trans
      ⟨fun h => mem_tot.2 fun τ _ => h τ, fun h τ => mem_tot.1 h τ ()⟩
  have h1 : shiftE l e 1 (P.ext (invL l (A O K))) =
      shiftE l e (j + 1) (P.Mext (invL l (A O K))) := by
    ext v
    rw [h0, mem_shiftE, mem_shiftE, mem_shiftE, smul_smul, ← Ezpow_add, neg_add]
  rw [PhiMod.filL, h1, h0]
  split_ifs with h
  · rw [inf_of_le_left fun _ => mem_shiftE_of_le h,
      sup_of_le_left fun _ => mem_shiftE_of_le (by omega)]
  · exact sup_of_le_right (inf_le_right.trans fun _ => mem_shiftE_of_le (by omega))

theorem jumps_rankOne (j : ℤ) : (rankOne O K l e fun _ : ZMod a => j).jumps = {j} := by
  ext i
  simp only [PhiMod.jumps, Set.mem_ofPred_eq, filL_rankOne, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hi
    exact h (by simp only [show i + 1 ≤ j ↔ i ≤ j by omega])
  · rintro rfl h
    rw [if_neg (by omega), if_pos le_rfl] at h
    have h1 : Ezpow K l e i • (bas () : Vec K a Unit) ∈ shiftE l e i
        ((rankOne O K l e fun _ : ZMod a => i).Mext (invL l (A O K))) := by
      rw [mem_shiftE, smul_smul, Ezpow_neg_mul, one_smul]
      exact PhiMod.Mext_mono _ (le_away _ _)
        ((rankOne O K l e fun _ : ZMod a => i).bas_mem_M ())
    rw [← h, mem_shiftE, smul_smul, ← Ezpow_add] at h1
    have h2 := mem_tot.1 h1 0 ()
    simp only [bas, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      Ezpow_mem_invL_A_iff] at h2
    omega

end Examples

section Examples

variable [CompleteSpace K] {j : ℤ} (h₁ : -(η : ℤ) ≤ j) (h₂ : j ≤ H)

theorem Lc_rankOneDat (χ : TameGal K l e a →* O) :
    (rankOneDat O K l e a η H j h₁ h₂ χ).Lc
        ((rankOneDat O K l e a η H j h₁ h₂ χ).cls (Ezpow K l e (-1) • bas ())) =
      (((j + 1) * e * l : ℤ) : K) •
        (rankOneDat O K l e a η H j h₁ h₂ χ).cls (Ezpow K l e (-1) • bas ()) := by
  obtain ⟨γ, hγ, h⟩ := exists_EN_bas_rankOne (O := O) (K := K) (l := l) (e := e) (a := a) j
  have h2 : E K l e * Ezpow K l e (-1) = 1 := by simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
  have h3 : (rankOneDat O K l e a η H j h₁ h₂ χ).EN (Ezpow K l e (-1) • bas ()) =
      (((j + 1) * e * l : ℤ) : K) • Ezpow K l e (-1) • (bas () : Vec K a Unit) +
        (γ - ((j + 1) * e : ℤ)) • bas () := by
    rw [PhiMod.EN_apply, PhiMod.conn_smul, smul_add, smul_comm (E K l e) (Ezpow K l e (-1)),
      ← PhiMod.EN_apply]
    erw [h]
    rw [Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul K⟦X⟧]
    simp only [smul_smul, ← add_smul]
    congr 1
    rw [E_mul_N_Ezpow, N_E]
    rw [E] at h2 ⊢
    push_cast
    linear_combination (γ - (j + 1) * e) * h2
  rw [BKDat.Lc_cls, h3, map_add, map_smul, add_eq_left, PhiMod.cls_eq_zero_iff]
  exact PhiMod.smul_mem_Man _ (sub_mem (S_le_R l e hγ) (intCast_mem _ _))
    (PhiMod.M_le_Man _ (PhiMod.bas_mem_M _ _))

theorem cls_mem_Z_rankOneDat (hη : 1 ≤ η) :
    (rankOneDat O K l e a η H j h₁ h₂ 1).cls (Ezpow K l e (-1) • bas ()) ∈
        (rankOneDat O K l e a η H j h₁ h₂ 1).Z ∧
      (rankOneDat O K l e a η H j h₁ h₂ 1).cls (Ezpow K l e (-1) • bas ()) ≠ 0 := by
  refine ⟨Descent.cls_mem_Z _ ⟨mem_tot.2 fun τ i => ?_, fun g => ?_⟩, fun h => ?_⟩
  · have := Ezpow_mem_A (O := O) (K := K) (l := l) (e := e) (i := η + -1) (by omega)
    rw [Ezpow_add, Ezpow_natCast] at this
    simpa [bas] using this
  · ext τ i : 2
    refine (rankOneDesc_act j 1 g _ τ).trans ?_
    simpa [bas] using map_Ezpow l e _ (congrFun (ringAct_E g) τ) (-1)
  · have h1 := mem_tot.1 ((PhiMod.cls_eq_zero_iff _).1 h) 0 ()
    have h2 : E K l e * Ezpow K l e (-1) = 1 := by simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
    have h3 := eq_zero_of_E_mul (O := O) (g := Ezpow K l e (-1)) l e (by simpa [bas] using h1)
      fun n => by rw [h2, coeff_one, if_neg (by have := NeZero.pos e; omega)]
    exact Units.ne_zero _ h3

def splitDat (χ : TameGal K l e a →* O) : BKDat O K l e a (Unit ⊕ Unit) η H :=
  BKDat.plusDat (D := rankOneDat O K l e a η H j h₁ h₂ χ) (y := 0) (zero_mem _) (map_zero _)
    ⟨0, zero_mem _, by simp⟩ (by simp)

example (χ : TameGal K l e a →* O) :
    BKHom (rankOneDat O K l e a η H j h₁ h₂ χ) (splitDat h₁ h₂ χ) :=
  Descent.plusInl _ _ (zero_mem _)

end Examples

example : BKDat ℤ_[3] ℚ_[3] 3 2 1 Unit 1 2 := rankOneDat _ _ _ _ _ 1 2 (-1) (by simp) (by simp) 1

def Descent.plusProj {P : PhiMod O K l e a ι} (Δ : Descent P) {y : Vec K a ι}
    (hy : y ∈ P.Mext (invE l e (A O K))) (hinv : y ∈ Δ.inv) :
    Descent.Hom (Δ.plus hy hinv) (rankOneDesc 0 1) where
  toHom := P.plusProj hy
  app_act g w := by
    rw [← join_eta w, Descent.plus_act_join, P.plusProj_app, P.plusProj_app]
    ext τ i : 2
    refine Eq.trans ?_ (rankOneDesc_act 0 1 g _ τ).symm
    simp [ringAct_apply]


section Omega

omit [NeZero a] [TameDescentExponentData K l e a]

variable [TameDescentExponentData K l e 1]

omit [IsUltrametricDist K] in
theorem exists_algebraMap_eq_root (g : TameGal K l e 1) : ∃ c : O, algebraMap O K c = g.root 0 :=
  (IsUnitBall.mem_range_iff (O := O) (g.root 0)).2 (g.norm_root 0).le

variable (O) in

def omegaOne : TameGal K l e 1 →* O where
  toFun g := (exists_algebraMap_eq_root g).choose
  map_one' := IsUnitBall.inj (K := K) (by
    rw [(exists_algebraMap_eq_root _).choose_spec, TameGal.root_one, map_one])
  map_mul' g h := IsUnitBall.inj (K := K) (by
    rw [map_mul, (exists_algebraMap_eq_root _).choose_spec, (exists_algebraMap_eq_root _).choose_spec,
      (exists_algebraMap_eq_root _).choose_spec, TameGal.root_mul, Subsingleton.elim (0 - g.shift) 0])

omit [IsUltrametricDist K] in
theorem algebraMap_omegaOne (g : TameGal K l e 1) : algebraMap O K (omegaOne O g) = g.root 0 :=
  (exists_algebraMap_eq_root g).choose_spec


end Omega

end GlobalTheory.BK
end
end
