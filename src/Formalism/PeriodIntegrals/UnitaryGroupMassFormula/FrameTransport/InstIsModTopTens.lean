import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.StepTransl

section
noncomputable section

namespace PI.FT

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct

section Lin

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}

def Lm (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (B : Matrix (Fin (M + 1)) (Fin M) E) : Matrix (Fin M) (Fin (M + 1)) E :=
  J'⁻¹ * Formalism.UG.cT (σ : E →+* E) B * J

theorem Lm_mul {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
    {B : Matrix (Fin (M + 1)) (Fin M) E} (hJ' : J' = Formalism.UG.cT (σ : E →+* E) B * J * B)
    (hd : J'.det ≠ 0) : Lm σ J J' B * B = 1 := by
  have h : Lm σ J J' B * B = J'⁻¹ * J' := by
    rw [hJ']
    simp only [Lm, Matrix.mul_assoc]
  rw [h]
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd)

theorem rowJ_mul {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Fin 1 → Fin n → E)
    (C : Matrix (Fin n) (Fin m) E) (k : Fin m) :
    ((Matrix.of v).map σ * J * C) 0 k = hE σ J (v 0) (fun i => C i k) := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, hE, Formalism.UG.hform, Finset.sum_mul,
    mul_assoc, RingHom.coe_coe]
  first
    | rfl
    | (rw [Finset.sum_comm]; done)
    | (rw [Finset.sum_comm]
       exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    | (exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    | (simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
       rw [Finset.sum_comm]
       exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    | (simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
       exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

def Xc (x : Fin 1 → Fin (M + 1) → E) : Matrix (Fin (M + 1)) (Fin 1) E := (Matrix.of x)ᵀ

def qm (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (b : E) :
    Matrix (Fin 1) (Fin (M + 1)) E :=
  b⁻¹ • ((Matrix.of x).map σ * J)

def Rm (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (x : Fin 1 → Fin (M + 1) → E) (b : E) :
    Matrix (Fin M) (Fin (M + 1)) E :=
  Lm σ J J' B - (Lm σ J J' B * Xc x) * qm σ J x b

variable {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
  {B : Matrix (Fin (M + 1)) (Fin M) E} {x : Fin 1 → Fin (M + 1) → E} {b : E}

theorem qm_mul_Xc (hb : b ≠ 0) (hx : hE σ J (x 0) (x 0) = b) : qm σ J x b * Xc x = 1 := by
  have hc : (fun i => Xc x i 0) = x 0 := rfl
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [qm, Matrix.smul_mul, Matrix.smul_apply, rowJ_mul, hc, hx, Matrix.one_apply_eq, smul_eq_mul,
    inv_mul_cancel₀ hb]

theorem qm_mul_B (hxB : ∀ j, hE σ J (x 0) (fun i => B i j) = 0) : qm σ J x b * B = 0 := by
  ext i k
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rw [qm, Matrix.smul_mul, Matrix.smul_apply, rowJ_mul, hxB, smul_zero, Matrix.zero_apply]

theorem Rm_mul_Xc (hb : b ≠ 0) (hx : hE σ J (x 0) (x 0) = b) : Rm σ J J' B x b * Xc x = 0 := by
  rw [Rm, Matrix.sub_mul, Matrix.mul_assoc (Lm σ J J' B * Xc x), qm_mul_Xc σ hb hx, Matrix.mul_one,
    sub_self]

theorem Rm_mul_B (hLB : Lm σ J J' B * B = 1) (hxB : ∀ j, hE σ J (x 0) (fun i => B i j) = 0) :
    Rm σ J J' B x b * B = 1 := by
  rw [Rm, Matrix.sub_mul, Matrix.mul_assoc (Lm σ J J' B * Xc x), qm_mul_B σ hxB, Matrix.mul_zero,
    sub_zero, hLB]

theorem Xc_q_add_B_R (hb : b ≠ 0) (hx : hE σ J (x 0) (x 0) = b)
    (hxB : ∀ j, hE σ J (x 0) (fun i => B i j) = 0) (hLB : Lm σ J J' B * B = 1) :
    Xc x * qm σ J x b + B * Rm σ J J' B x b = 1 := by
  have h1 : Matrix.fromRows (qm σ J x b) (Rm σ J J' B x b) * Matrix.fromCols (Xc x) B = 1 := by
    rw [Matrix.fromRows_mul_fromCols, qm_mul_Xc σ hb hx, qm_mul_B σ hxB, Rm_mul_Xc σ hb hx,
      Rm_mul_B σ hLB hxB, Matrix.fromBlocks_one]
  have e : Fin 1 ⊕ Fin M ≃ Fin (M + 1) :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  have h2 := (Matrix.mul_eq_one_comm_of_equiv e).mp h1
  rwa [Matrix.fromCols_mul_fromRows] at h2

end Lin

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
variable (R : Type) [CommRing R] [Algebra F R]

theorem map_one_incl {n : Type} [Fintype n] [DecidableEq n] :
    (1 : Matrix n n E).map (inclR (F := F) (E := E) R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem formulaA {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
    {B : Matrix (Fin (M + 1)) (Fin M) E} (hLB : Lm σ J J' B * B = 1)
    (G : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) (G' : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (h : G * B.map (inclR (F := F) (E := E) R) = B.map (inclR (F := F) (E := E) R) * G') :
    G' = (Lm σ J J' B).map (inclR (F := F) (E := E) R) * G * B.map (inclR (F := F) (E := E) R) := by
  have hLB' : (Lm σ J J' B).map (inclR (F := F) (E := E) R) * B.map (inclR (F := F) (E := E) R) = 1 := by
    rw [← Matrix.map_mul, hLB, map_one_incl]
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hLB', Matrix.one_mul]

theorem formulaB {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
    {B : Matrix (Fin (M + 1)) (Fin M) E} {x : Fin 1 → Fin (M + 1) → E} {b : E}
    (hdec : Xc x * qm σ J x b + B * Rm σ J J' B x b = 1)
    (G : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) (G' : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (hX : G * (Xc x).map (inclR (F := F) (E := E) R) = (Xc x).map (inclR (F := F) (E := E) R))
    (h : G * B.map (inclR (F := F) (E := E) R) = B.map (inclR (F := F) (E := E) R) * G') :
    G = (Xc x).map (inclR (F := F) (E := E) R) * (qm σ J x b).map (inclR (F := F) (E := E) R) +
      B.map (inclR (F := F) (E := E) R) * G' * (Rm σ J J' B x b).map (inclR (F := F) (E := E) R) := by
  have h1 : (Xc x).map (inclR (F := F) (E := E) R) * (qm σ J x b).map (inclR (F := F) (E := E) R) +
      B.map (inclR (F := F) (E := E) R) * (Rm σ J J' B x b).map (inclR (F := F) (E := E) R) = 1 := by
    have e1 : (Xc x * qm σ J x b).map (inclR (F := F) (E := E) R) =
        (Xc x).map (inclR (F := F) (E := E) R) * (qm σ J x b).map (inclR (F := F) (E := E) R) := Matrix.map_mul
    have e2 : (B * Rm σ J J' B x b).map (inclR (F := F) (E := E) R) =
        B.map (inclR (F := F) (E := E) R) * (Rm σ J J' B x b).map (inclR (F := F) (E := E) R) := Matrix.map_mul
    rw [← e1, ← e2, ← Matrix.map_add _ (map_add _), hdec, map_one_incl]
  calc G = G * 1 := (Matrix.mul_one G).symm
    _ = _ := by
      rw [← h1, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX, h]

theorem stab_mul_Xc {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
    (g : Hstab R σ J x) :
    ((HA.mat R σ J (g : HA R σ J) : GL (Fin (M + 1)) (R ⊗[F] E)) :
      Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * (Xc x).map (inclR (F := F) (E := E) R) =
      (Xc x).map (inclR (F := F) (E := E) R) := by
  have hg := g.2
  simp only [Hstab, MulAction.mem_stabilizer_iff] at hg
  delta actTup ratTup at hg
  ext i j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have h2 := congrFun (congrFun hg 0) i
  rw [Matrix.mul_apply]
  simp only [Xc, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [← h2]
  rfl

theorem cT_map_incl {m n : ℕ} (a : Matrix (Fin m) (Fin n) E) :
    (Formalism.UG.cT (σ : E →+* E) a).map (inclR (F := F) (E := E) R) =
      Formalism.UG.cT (sigR R σ) (a.map (inclR (F := F) (E := E) R)) := by
  ext i j
  simp [Formalism.UG.cT, inclR, sigR]

theorem mem_HFinIn_iff (hinj : Function.Injective (inclR (F := F) (E := E) R))
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : HA R σ J) :
    toHR g ∈ HFinIn R σ J ↔
      (∃ a : Matrix (Fin n) (Fin n) E, ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (R ⊗[F] E)) = a.map (inclR (F := F) (E := E) R)) ∧
      (∃ a : Matrix (Fin n) (Fin n) E, (((HA.mat R σ J g)⁻¹ : GL (Fin n) (R ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (R ⊗[F] E)) = a.map (inclR (F := F) (E := E) R)) := by
  simp only [HFinIn]
  rw [Subgroup.mem_subgroupOf]
  simp only [HFin, Subgroup.mem_map, Formalism.UG.bc, Formalism.UG.UJ, toHR, HA.mat]
  have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) E => M.map (inclR (F := F) (E := E) R)) :=
    fun M N h => Matrix.ext fun i j => hinj (by simpa using congrArg (fun P => P i j) h)
  constructor
  · rintro ⟨y, -, hy⟩
    rw [← hy]
    exact ⟨⟨(y : Matrix (Fin n) (Fin n) E), rfl⟩, ⟨((y⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E), rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    have h1 : a * a' = 1 := by
      apply inj
      show (a * a').map (inclR (F := F) (E := E) R) = (1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (E := E) R)
      rw [Matrix.map_mul, ← ha, ← ha', Units.mul_inv, map_one_incl]
    have h2 : a' * a = 1 := by
      apply inj
      show (a' * a).map (inclR (F := F) (E := E) R) = (1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (E := E) R)
      rw [Matrix.map_mul, ← ha, ← ha', Units.inv_mul, map_one_incl]
    refine ⟨⟨a, a', h1, h2⟩, ?_, Units.ext ha.symm⟩
    show Formalism.UG.cT (σ : E →+* E) a * J * a = J
    apply inj
    simp only [Matrix.map_mul, cT_map_incl, ← ha]
    have hg := g.2
    simp only [HA, HR, Formalism.UG.UJ, JR, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_setOf_eq] at hg
    exact hg

end Tens

end PI.FT
end
end

section
noncomputable section

namespace PI.FT

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct

section Mat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
  {R : Type} [CommRing R] [Algebra F R]

abbrev mt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : HA R σ J) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))

abbrev mtI {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : HA R σ J) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (((HA.mat R σ J g)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))

end Mat

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

instance instIsModTopTens : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

instance instContAddTens : ContinuousAdd (R ⊗[F] E) :=
  IsModuleTopology.toContinuousAdd R (R ⊗[F] E)



theorem cont_HA_iff {T : Type*} [TopologicalSpace T] {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (f : T → HA R σ J) :
    Continuous f ↔ Continuous (fun t => mt (f t)) ∧ Continuous (fun t => mtI (f t)) := by
  constructor
  · intro hf
    have h1 : Continuous (fun t => ((toHR (f t) : HR R σ J) : GL (Fin n) (R ⊗[F] E))) :=
      continuous_subtype_val.comp hf
    exact ⟨Units.continuous_val.comp h1, Units.continuous_coe_inv.comp h1⟩
  · rintro ⟨h1, h2⟩
    have h3 : Continuous (fun t => ((toHR (f t) : HR R σ J) : GL (Fin n) (R ⊗[F] E))) :=
      Units.continuous_iff.2 ⟨h1, h2⟩
    exact h3.subtype_mk (fun t => (toHR (f t)).2)


end Cont

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

local notation "ι" => inclR (F := F) (E := E) (AF F)

theorem frame_formulas {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
    {J' : Matrix (Fin M) (Fin M) E} {x : Fin 1 → Fin (M + 1) → E} {β : F}
    {B : Matrix (Fin (M + 1)) (Fin M) E} (hH : FrameHyp F E σ M J J' x β B)
    (e : Hstab (AF F) σ J x ≃* HA (AF F) σ J')
    (he : ∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) :
    (∀ g : Hstab (AF F) σ J x,
      mt (e g) = (Lm σ J J' B).map ι * mt (g : HA (AF F) σ J) * B.map ι) ∧
    (∀ g : Hstab (AF F) σ J x,
      mt (g : HA (AF F) σ J) = (Xc x).map ι * (qm σ J x (algebraMap F E β)).map ι +
        B.map ι * mt (e g) * (Rm σ J J' B x (algebraMap F E β)).map ι) := by
  obtain ⟨-, hβ, hx, hxB, hJ', -, hd⟩ := hH
  have hb : algebraMap F E β ≠ 0 := fun h =>
    hβ ((algebraMap F E).injective (h.trans (map_zero _).symm))
  have hLB := Lm_mul σ hJ' hd
  have hdec := Xc_q_add_B_R σ hb hx hxB hLB
  exact ⟨fun g => formulaA σ (AF F) hLB _ _ (he g),
    fun g => formulaB σ (AF F) hdec _ _ (stab_mul_Xc σ (AF F) g) (he g)⟩

theorem mtI_eq {M' : ℕ} {J' : Matrix (Fin M') (Fin M') E}
    {K : Type} [Group K] (e : K ≃* HA (AF F) σ J') (g : K) :
    mtI (e g) = mt (e g⁻¹) := by
  rw [map_inv e g]
  rfl



instance instNontrivialAF : Nontrivial (AF F) :=
  inferInstanceAs (Nontrivial (NumberField.InfiniteAdeleRing F ×
    IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))

end Frame

end PI.FT
end
end
