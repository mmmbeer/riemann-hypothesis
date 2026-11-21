import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.QuotIntegrableIffCutoff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemCentIffTwConj

section
open Matrix

noncomputable section

namespace GlobalTheory.Tw

section Theta
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

def PhiGL (n : ℕ) (R : Type) [CommRing R] : GL (Fin n) R :=
  ⟨Phi n R, (Phi n R)ᵀ, Model.Phi_mul_transpose, Model.transpose_mul_Phi⟩

omit [StarRing R] in
@[simp] theorem PhiGL_val : (PhiGL n R).val = Phi n R := rfl

omit [StarRing R] in
@[simp] theorem PhiGL_inv_val : (PhiGL n R)⁻¹.val = (Phi n R)ᵀ := rfl

omit [StarRing R] in
theorem Phi_inv : (Phi n R)⁻¹ = (Phi n R)ᵀ := Matrix.inv_eq_right_inv Model.Phi_mul_transpose

def thetaGL (g : GL (Fin n) R) : GL (Fin n) R := PhiGL n R * star g⁻¹ * (PhiGL n R)⁻¹

theorem thetaGL_val (g : GL (Fin n) R) : (thetaGL g).val = theta g.val := by
  simp [thetaGL, theta, Matrix.star_eq_conjTranspose, Phi_inv]

theorem thetaGL_thetaGL (g : GL (Fin n) R) : thetaGL (thetaGL g) = g :=
  Units.ext (by rw [thetaGL_val, thetaGL_val, Model.theta_theta g.isUnit])

theorem thetaGL_mul (g h : GL (Fin n) R) : thetaGL (g * h) = thetaGL g * thetaGL h :=
  Units.ext (by simp only [Units.val_mul, thetaGL_val, Model.theta_mul])

theorem star_PhiGL : star (PhiGL n R) = (PhiGL n R)⁻¹ :=
  Units.ext (by simp [Matrix.star_eq_conjTranspose, Model.Phi_conjTranspose, Phi_inv])

end Theta

structure PFlag (n : ℕ) (k : Type) [CommRing k] where

  carrier : Set (Submodule k (Fin n → k))
  chain : IsChain (· ≤ ·) carrier
  bot_mem : ⊥ ∈ carrier
  top_mem : ⊤ ∈ carrier

namespace PFlag

section Ring
variable {n : ℕ} {k : Type} [CommRing k] (F : PFlag n k)

def triv (n : ℕ) (k : Type) [CommRing k] : PFlag n k where
  carrier := {⊥, ⊤}
  chain := by
    rintro _ (rfl | rfl) _ (rfl | rfl) _ <;> simp
  bot_mem := by simp
  top_mem := by simp

def single (V : Submodule k (Fin n → k)) : PFlag n k where
  carrier := {⊥, V, ⊤}
  chain := by
    rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) _ <;> simp
  bot_mem := by simp
  top_mem := by simp

def pred (V : Submodule k (Fin n → k)) : Submodule k (Fin n → k) := sSup {V' | V' ∈ F.carrier ∧ V' < V}

theorem pred_le (V : Submodule k (Fin n → k)) : F.pred V ≤ V := sSup_le fun _ h => h.2.le

theorem le_pred {V V' : Submodule k (Fin n → k)} (h : V' ∈ F.carrier) (hlt : V' < V) : V' ≤ F.pred V :=
  le_sSup ⟨h, hlt⟩

def lieQ : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := {X | ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ V}
  add_mem' hX hY V hV v hv := by rw [add_mulVec]; exact V.add_mem (hX V hV v hv) (hY V hV v hv)
  zero_mem' V _ v _ := by simp
  smul_mem' c X hX V hV v hv := by rw [smul_mulVec]; exact V.smul_mem c (hX V hV v hv)

def lieN : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := {X | ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ F.pred V}
  add_mem' hX hY V hV v hv := by rw [add_mulVec]; exact (F.pred V).add_mem (hX V hV v hv) (hY V hV v hv)
  zero_mem' V _ v _ := by simp
  smul_mem' c X hX V hV v hv := by rw [smul_mulVec]; exact (F.pred V).smul_mem c (hX V hV v hv)

variable {F}


theorem one_mem_lieQ : (1 : Matrix (Fin n) (Fin n) k) ∈ F.lieQ := fun V _ v hv => by simpa using hv

theorem mul_mem_lieQ {X Y : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieQ) (hY : Y ∈ F.lieQ) : X * Y ∈ F.lieQ :=
  fun V hV v hv => by rw [← mulVec_mulVec]; exact hX V hV _ (hY V hV v hv)

theorem mulVec_mem_pred {X : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieQ) (V : Submodule k (Fin n → k)) {v : Fin n → k}
    (hv : v ∈ F.pred V) : X *ᵥ v ∈ F.pred V := by
  have : F.pred V ≤ (F.pred V).comap X.mulVecLin :=
    sSup_le fun V' h w hw => F.le_pred h.1 h.2 (hX V' h.1 w hw)
  exact this hv

theorem lieQ_mul_lieN {X Y : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieQ) (hY : Y ∈ F.lieN) : X * Y ∈ F.lieN :=
  fun V hV v hv => by rw [← mulVec_mulVec]; exact mulVec_mem_pred hX V (hY V hV v hv)

theorem lieN_mul_lieQ {X Y : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieN) (hY : Y ∈ F.lieQ) : X * Y ∈ F.lieN :=
  fun V hV v hv => by rw [← mulVec_mulVec]; exact hX V hV _ (hY V hV v hv)

variable (F)

def stab : Subgroup (GL (Fin n) k) where
  carrier := {g | g.val ∈ F.lieQ ∧ g⁻¹.val ∈ F.lieQ}
  mul_mem' hg hh := ⟨mul_mem_lieQ hg.1 hh.1, by rw [_root_.mul_inv_rev]; exact mul_mem_lieQ hh.2 hg.2⟩
  one_mem' := ⟨one_mem_lieQ, one_mem_lieQ⟩
  inv_mem' hg := ⟨hg.2, hg.1⟩

def unip : Subgroup (GL (Fin n) k) where
  carrier := {g | g ∈ F.stab ∧ g.val - 1 ∈ F.lieN}
  mul_mem' {g h} hg hh := ⟨mul_mem hg.1 hh.1, by
    have : (g * h).val - 1 = (g.val - 1) * h.val + (h.val - 1) := by rw [Units.val_mul]; noncomm_ring
    rw [this]; exact add_mem (lieN_mul_lieQ hg.2 hh.1.1) hh.2⟩
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, by
    have : g⁻¹.val - 1 = -(g⁻¹.val * (g.val - 1)) := by rw [mul_sub, Units.inv_mul]; simp
    rw [this]; exact neg_mem (lieQ_mul_lieN hg.1.2 hg.2)⟩


variable {F}

theorem mem_stab_iff_map {g : GL (Fin n) k} : g ∈ F.stab ↔ ∀ V ∈ F.carrier, V.map g.val.mulVecLin = V := by
  constructor
  · intro hg V hV
    refine le_antisymm ?_ fun v hv => ⟨g⁻¹.val *ᵥ v, hg.2 V hV v hv, by simp [mulVec_mulVec]⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hg.1 V hV v hv
  · intro h
    refine ⟨fun V hV v hv => (h V hV).le ⟨v, hv, rfl⟩, fun V hV v hv => ?_⟩
    obtain ⟨w, hw, rfl⟩ := (h V hV).ge hv
    simpa [mulVec_mulVec] using hw

end Ring

section Field
variable {n : ℕ} {k : Type} [Field k] {F : PFlag n k}

theorem mem_stab_iff {g : GL (Fin n) k} : g ∈ F.stab ↔ g.val ∈ F.lieQ := by
  refine ⟨fun h => h.1, fun h => mem_stab_iff_map.2 fun V hV => ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨v, hv, rfl⟩; exact h V hV v hv) ?_
  refine (Submodule.equivMapOfInjective _ (fun v w hvw => ?_) V).finrank_eq.symm
  have := congrArg (g⁻¹.val *ᵥ ·) hvw
  simpa [mulVec_mulVec] using this

end Field

section Complex
variable {n : ℕ} (F : PFlag n ℂ)

theorem isClosed_lieQ : IsClosed (F.lieQ : Set (Matrix (Fin n) (Fin n) ℂ)) := F.lieQ.closed_of_finiteDimensional

theorem isClosed_stab : IsClosed (F.stab : Set (GL (Fin n) ℂ)) :=
  (F.isClosed_lieQ.preimage Units.continuous_val).inter (F.isClosed_lieQ.preimage Units.continuous_coe_inv)

end Complex

end PFlag

def perp {n : ℕ} (V : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) where
  carrier := {w | ∀ v ∈ V, w ⬝ᵥ star v = 0}
  add_mem' hw hw' v hv := by rw [add_dotProduct, hw v hv, hw' v hv, add_zero]
  zero_mem' v _ := by simp
  smul_mem' c w hw v hv := by rw [smul_dotProduct, hw v hv, smul_zero]

def PFlag.summand {n : ℕ} (F : PFlag n ℂ) (V : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) := V ⊓ perp (F.pred V)

section Perp
variable {n : ℕ}


theorem dot_star_comm_zero {v w : Fin n → ℂ} (h : v ⬝ᵥ star w = 0) : w ⬝ᵥ star v = 0 := by
  have := congrArg star h
  rwa [star_zero, ← star_dotProduct_star, star_star] at this

theorem perp_anti {V V' : Submodule ℂ (Fin n → ℂ)} (h : V ≤ V') : perp V' ≤ perp V := fun _ hw v hv => hw v (h hv)

open scoped ComplexOrder in
theorem eq_zero_of_dot_star {v : Fin n → ℂ} (h : v ⬝ᵥ star v = 0) : v = 0 := dotProduct_self_star_eq_zero.1 h

theorem eq_zero_of_mem_perp {V : Submodule ℂ (Fin n → ℂ)} {v : Fin n → ℂ} (h : v ∈ V) (h' : v ∈ perp V) : v = 0 :=
  eq_zero_of_dot_star (h' v h)

theorem sup_perp (V : Submodule ℂ (Fin n → ℂ)) : V ⊔ perp V = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨y, hy, w, hw, h⟩ := Submodule.exists_add_mem_mem_orthogonal
    (K := V.comap (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap) (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin n))
  refine Submodule.mem_sup.2 ⟨y.ofLp, hy, w.ofLp, fun v hv => ?_, (congrArg WithLp.ofLp h).symm⟩
  have := hw (WithLp.toLp 2 v) hv
  rwa [EuclideanSpace.inner_eq_star_dotProduct] at this

theorem perp_perp (V : Submodule ℂ (Fin n → ℂ)) : perp (perp V) = V := by
  have h1 : V ≤ perp (perp V) := fun v hv w hw => dot_star_comm_zero (hw v hv)
  refine le_antisymm (fun z hz => ?_) h1
  obtain ⟨v, hv, u, hu, rfl⟩ := Submodule.mem_sup.1 ((sup_perp V).ge (Submodule.mem_top (x := z)))
  have : u = 0 := eq_zero_of_mem_perp hu (by simpa using sub_mem hz (h1 hv))
  simpa [this] using hv

namespace PFlag
variable {F : PFlag n ℂ}






def realScalars (F : PFlag n ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | ∀ V ∈ F.carrier, ∃ c : ℝ, ∀ v ∈ F.summand V, X *ᵥ v = c • v}
  add_mem' hX hY V hV := by
    obtain ⟨c, hc⟩ := hX V hV
    obtain ⟨d, hd⟩ := hY V hV
    exact ⟨c + d, fun v hv => by rw [add_mulVec, hc v hv, hd v hv, add_smul]⟩
  zero_mem' V _ := ⟨0, fun v _ => by simp⟩
  smul_mem' r X hX V hV := by
    obtain ⟨c, hc⟩ := hX V hV
    exact ⟨r * c, fun v hv => by rw [smul_mulVec, hc v hv, mul_smul]⟩



end PFlag

end Perp

theorem commute_of_commute_separable {n : ℕ} {A g h : Matrix (Fin n) (Fin n) ℂ} (hA : A.charpoly.Separable)
    (hg : Commute A g) (hh : Commute A h) : Commute g h := by
  set f := Matrix.toLin' A
  have hc : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' g) := hg.map Matrix.toLinAlgEquiv'
  have hfh : Commute f (Matrix.toLin' h) := hh.map Matrix.toLinAlgEquiv'
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤
      LinearMap.ker (Matrix.toLin' g * Matrix.toLin' h - Matrix.toLin' h * Matrix.toLin' g) := fun μ v hv => by
    have h1 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hc]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have hs : ∀ w ∈ Module.End.maxGenEigenspace f μ, ∃ c : ℂ, c • v = w := fun w hw => by
      have h2 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨w, hw⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    obtain ⟨c, hc⟩ := hs _ (Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv)
    obtain ⟨d, hd⟩ := hs _ (Module.End.mapsTo_maxGenEigenspace_of_comm hfh μ hv)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, ← hc, ← hd, map_smul, map_smul,
      ← hc, ← hd, smul_comm, sub_self]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero] at h3
  exact Matrix.toLinAlgEquiv'.injective (by rw [map_mul, map_mul]; exact h3)

end GlobalTheory.Tw
end
end

section
open Matrix MeasureTheory Topology
open scoped Kronecker ContDiff

noncomputable section

namespace GlobalTheory.Tw

abbrev GP (a b : ℕ) (R : Type) [CommRing R] : Type := GL (Fin a) R × GL (Fin b) R

section Alg
variable {a b : ℕ} {R : Type} [CommRing R] [StarRing R]

def PhiG (a b : ℕ) (R : Type) [CommRing R] : GP a b R := (PhiGL a R, PhiGL b R)

def th0 : MulAut (GP a b R) where
  toFun g := star g⁻¹
  invFun g := star g⁻¹
  left_inv g := by simp [star_inv]
  right_inv g := by simp [star_inv]
  map_mul' g h := by simp

def thetaG : MulAut (GP a b R) where
  toFun g := (thetaGL g.1, thetaGL g.2)
  invFun g := (thetaGL g.1, thetaGL g.2)
  left_inv _ := Prod.ext (thetaGL_thetaGL _) (thetaGL_thetaGL _)
  right_inv _ := Prod.ext (thetaGL_thetaGL _) (thetaGL_thetaGL _)
  map_mul' _ _ := Prod.ext (thetaGL_mul _ _) (thetaGL_mul _ _)

theorem cartan_involution_apply (g : GP a b R) : th0 g = star g⁻¹ := rfl

@[simp] theorem cartan_involution_involutive (g : GP a b R) : th0 (th0 g) = g := by
  rw [cartan_involution_apply, cartan_involution_apply, star_inv, star_star, inv_inv]

@[simp] theorem thetaG_thetaG (g : GP a b R) : thetaG (thetaG g) = g := by
  exact Prod.ext (thetaGL_thetaGL g.1) (thetaGL_thetaGL g.2)

theorem cartan_involution_frobenius : th0 (PhiG a b R) = PhiG a b R := by
  rw [cartan_involution_apply]
  refine Prod.ext ?_ ?_ <;> simp [PhiG, star_inv, star_PhiGL]

def twAct (x δ y : GP a b R) : GP a b R := x * δ * thetaG y

def toTh0 (g : GP a b R) : GP a b R := g * PhiG a b R

def centG (δ : GP a b R) : Subgroup (GP a b R) where
  carrier := {g | g * δ = δ * thetaG g}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [map_mul, mul_assoc, hh, ← mul_assoc, hg, mul_assoc]
  one_mem' := by simp
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [map_inv, eq_mul_inv_iff_mul_eq, mul_assoc, ← hg, inv_mul_cancel_left]

def IsTwRep {M : Type} [Monoid M] (H : Subgroup (GP a b R)) (Ht : Set (GP a b R)) (π : H →* M) (πt : GP a b R → M) : Prop :=
  ∀ δ ∈ Ht, IsUnit (πt δ) ∧ ∀ h₁ h₂ : H, πt (twAct h₁ δ h₂) = π h₁ * πt δ * π h₂

end Alg

abbrev GR (a b : ℕ) : Type := GP a b ℂ

abbrev LieG (a b : ℕ) : Type := Matrix (Fin a) (Fin a) ℂ × Matrix (Fin b) (Fin b) ℂ

variable {a b : ℕ}

instance secondCountable_GLC (n : ℕ) : SecondCountableTopology (GL (Fin n) ℂ) :=
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

instance locallyCompact_GLC (n : ℕ) : LocallyCompactSpace (GL (Fin n) ℂ) :=
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  inferInstance

instance measurableSpace_GR : MeasurableSpace (GR a b) := borel _

instance borelSpace_GR : BorelSpace (GR a b) := ⟨rfl⟩

def mat : GR a b →* LieG a b := (Units.coeHom _).prodMap (Units.coeHom _)

theorem mat_apply (g : GR a b) : mat g = (g.1.val, g.2.val) := rfl

theorem mat_star (g : GR a b) : mat (star g) = star (mat g) := rfl

theorem mat_injective : Function.Injective (mat : GR a b → LieG a b) := by
  intro g h e
  rw [mat_apply, mat_apply, Prod.mk.injEq] at e
  exact Prod.ext (Units.ext e.1) (Units.ext e.2)

@[simp] theorem mat_mul_inv (g : GR a b) : mat g * mat g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

@[simp] theorem mat_inv_mul (g : GR a b) : mat g⁻¹ * mat g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

def expG (X : LieG a b) : GR a b := ((Matrix.isUnit_exp X.1).unit, (Matrix.isUnit_exp X.2).unit)

def KR (a b : ℕ) : Subgroup (GR a b) := (th0 : MulAut (GR a b)).toMonoidHom.eqLocus (MonoidHom.id _)

theorem mem_KR {k : GR a b} : k ∈ KR a b ↔ th0 k = k := by
  exact Iff.rfl

theorem mem_KR_iff_star {k : GR a b} : k ∈ KR a b ↔ star k = k⁻¹ := by
  rw [mem_KR, cartan_involution_apply, star_inv, inv_eq_iff_eq_inv]

theorem mem_KR_iff_mat {k : GR a b} : k ∈ KR a b ↔ mat k * star (mat k) = 1 := by
  rw [mem_KR_iff_star, eq_comm, ← mul_eq_one_iff_inv_eq, ← mat_injective.eq_iff, map_mul, map_one, mat_star]

theorem mem_KR_iff_unitary {k : GR a b} :
    k ∈ KR a b ↔ k.1.val ∈ unitaryGroup (Fin a) ℂ ∧ k.2.val ∈ unitaryGroup (Fin b) ℂ := by
  rw [mem_KR_iff_mat, mat_apply, Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  simp only [Prod.ext_iff, Prod.fst_mul, Prod.snd_mul, Prod.fst_star, Prod.snd_star, Prod.fst_one, Prod.snd_one]

theorem PhiG_mem_KR : PhiG a b ℂ ∈ KR a b := by
  exact mem_KR.2 cartan_involution_frobenius

theorem isCompact_unitary_GL (n : ℕ) : IsCompact {k : GL (Fin n) ℂ | k.val ∈ unitaryGroup (Fin n) ℂ} := by
  have hU : IsCompact (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    have hcl : IsClosed (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
      have e : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
          (fun A : Matrix (Fin n) (Fin n) ℂ => A * star A) ⁻¹' {1} := by
        ext A; exact Matrix.mem_unitaryGroup_iff
      rw [e]
      exact isClosed_singleton.preimage (continuous_id.mul continuous_star)
    have hbd : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ⊆
        Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1 := by
      intro A hA i _ j _
      have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hA) i) i
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
      simp only [Matrix.star_apply, Complex.star_def, Complex.mul_conj] at h
      have h2 : ∑ k, Complex.normSq (A i k) = 1 := by exact_mod_cast h
      have h3 : Complex.normSq (A i j) ≤ 1 :=
        h2 ▸ Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (A i k)) (Finset.mem_univ j)
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Complex.normSq_eq_norm_sq] at h3
      nlinarith [norm_nonneg (A i j)]
    exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1).of_isClosed_subset hcl hbd
  have : CompactSpace (unitaryGroup (Fin n) ℂ) := isCompact_iff_compactSpace.1 hU
  let φ : unitaryGroup (Fin n) ℂ → GL (Fin n) ℂ := fun u =>
    ⟨u.1, star u.1, Unitary.mul_star_self_of_mem u.2, Unitary.star_mul_self_of_mem u.2⟩
  have hφ : Continuous φ :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  have hr : Set.range φ = {k : GL (Fin n) ℂ | k.val ∈ unitaryGroup (Fin n) ℂ} := by
    ext k
    constructor
    · rintro ⟨u, rfl⟩
      exact u.2
    · intro hk
      exact ⟨⟨k.val, hk⟩, Units.ext rfl⟩
  rw [← hr]
  exact isCompact_range hφ

theorem isCompact_KR : IsCompact (KR a b : Set (GR a b)) := by
  have e : (KR a b : Set (GR a b)) = {k : GL (Fin a) ℂ | k.val ∈ unitaryGroup (Fin a) ℂ} ×ˢ
      {k : GL (Fin b) ℂ | k.val ∈ unitaryGroup (Fin b) ℂ} := by
    ext k
    exact mem_KR_iff_unitary
  rw [e]
  exact (isCompact_unitary_GL a).prod (isCompact_unitary_GL b)

instance compactSpace_KR : CompactSpace (KR a b) := isCompact_iff_compactSpace.1 isCompact_KR

def haarK (a b : ℕ) : Measure (KR a b) := Measure.haarMeasure ⊤

instance : (haarK a b).IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _

instance : IsProbabilityMeasure (haarK a b) := ⟨Measure.haarMeasure_self (K₀ := ⊤)⟩

def pSp (a b : ℕ) : Submodule ℝ (LieG a b) := selfAdjoint.submodule ℝ (LieG a b)

theorem mem_pSp {X : LieG a b} : X ∈ pSp a b ↔ star X = X := by
  exact selfAdjoint.mem_iff

def AdLie (g : GR a b) : LieG a b →ₗ[ℝ] LieG a b := LinearMap.mulLeftRight ℝ (mat g, mat g⁻¹)

theorem AdLie_apply (g : GR a b) (X : LieG a b) : AdLie g X = mat g * X * mat g⁻¹ := rfl

def dth0 : LieG a b →ₗ[ℝ] LieG a b where
  toFun X := -star X
  map_add' X Y := by rw [star_add, neg_add]
  map_smul' c X := by simp

theorem diff_cartan_involution_apply (X : LieG a b) : dth0 X = -star X := rfl

def dtheta : LieG a b →ₗ[ℝ] LieG a b := AdLie (PhiG a b ℂ) ∘ₗ dth0

def AdT (δ : GR a b) : LieG a b →ₗ[ℝ] LieG a b := AdLie δ ∘ₗ dtheta

theorem AdLie_mul (g h : GR a b) : AdLie (g * h) = AdLie g ∘ₗ AdLie h := by
  refine LinearMap.ext fun X => ?_
  simp only [LinearMap.comp_apply, AdLie_apply, map_mul, _root_.mul_inv_rev, mul_assoc]

@[simp] theorem AdLie_one : AdLie (1 : GR a b) = LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  simp [AdLie_apply]

theorem AdT_eq (δ : GR a b) : AdT δ = AdLie (toTh0 δ) ∘ₗ dth0 := by
  simp only [AdT, dtheta, toTh0, AdLie_mul, LinearMap.comp_assoc]

theorem AdLie_mem_pSp {k : GR a b} (hk : k ∈ KR a b) {X : LieG a b} (hX : X ∈ pSp a b) : AdLie k X ∈ pSp a b := by
  rw [mem_pSp] at hX ⊢
  have hk' := mem_KR_iff_star.1 hk
  have e1 : star (mat k) = mat k⁻¹ := by rw [← mat_star, hk']
  have e2 : star (mat k⁻¹) = mat k := by rw [← mat_star, star_inv, hk', inv_inv]
  rw [AdLie_apply, star_mul, star_mul, e1, e2, hX, mul_assoc]

theorem AdT_mem_pSp {k : GR a b} (hk : k ∈ KR a b) {X : LieG a b} (hX : X ∈ pSp a b) : AdT k X ∈ pSp a b := by
  rw [AdT_eq, LinearMap.comp_apply]
  apply AdLie_mem_pSp (mul_mem hk PhiG_mem_KR)
  rw [diff_cartan_involution_apply, mem_pSp.1 hX]
  exact neg_mem hX

end GlobalTheory.Tw
end
end
