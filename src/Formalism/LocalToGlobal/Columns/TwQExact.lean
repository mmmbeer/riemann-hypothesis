import Formalism.LocalToGlobal.Columns.TwQDefs
import Formalism.LocalToGlobal.Columns.MtHeckeKv
import Mathlib
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Columns.AdjointFrobeniusPreservesRamified

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG

section QSurj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

variable (ST SG Q) in

structure QOff : Prop where
  off : ∀ (P : Q) (P' : Pl E), P' ∈ ST ∨ P' ∈ SG → ¬ IsOver (qv F P.1) P'
  inj : ∀ P P' : Q, qv F P.1 = qv F P'.1 → P = P'

def QIntGL {v : HeightOneSpectrum (𝓞 F)} (k : GL (Fin n) (v.adicCompletion F)) : Prop :=
  (∀ i j, ((k : Matrix (Fin n) (Fin n) _) i j) ∈ v.adicCompletionIntegers F) ∧
    (∀ i j, (((k⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j) ∈ v.adicCompletionIntegers F)

variable (ST SG) in

def FrLat (q : QLoc hc n Q Θ) : Prop :=
  ∀ (x : UAd hc n) (p : DecoF E n ST SG Q), decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = p.deco → ∀ P : Q,
    QIntGL ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x)

def QLift (q : QLoc hc n Q Θ) : Prop :=
  ∀ (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F)), QIntGL k →
    ∃ κ : GL (Fin n) (E ⊗[F] (qv F P.1).adicCompletion F),
      κ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) ((qv F P.1).adicCompletion F) ∧
      κ ∈ stabGL (Formalism.L2.Herm.locL (qv F P.1) (stdLat E n)) ∧
      bc ((RingHom.fst _ _).comp (q.sp P).toRingHom) κ = k

theorem qdf_at_put_ne (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (v : HeightOneSpectrum (𝓞 F))
    (hv : qv F P.1 ≠ v) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : q.at P (x * rll_put n v g) = q.at P x := by
  show bc _ (bc (prV (E := E) (qv F P.1)) (x * rll_put n v g)) = _
  rw [map_mul, rll_put_ne n v (qv F P.1) hv g, mul_one]

theorem qdf_at_put_self (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (g : GL (Fin n) (E ⊗[F] (qv F P.1).adicCompletion F)) :
    q.at P (x * rll_put n (qv F P.1) g) = q.at P x * bc ((RingHom.fst _ _).comp (q.sp P).toRingHom) g := by
  show bc _ (bc (prV (E := E) (qv F P.1)) (x * rll_put n (qv F P.1) g)) = _
  rw [map_mul, rll_put_self, map_mul]

theorem qdf_inv_mem_UPts {v : HeightOneSpectrum (𝓞 F)} {κ : GL (Fin n) (E ⊗[F] v.adicCompletion F)}
    (h : κ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F)) :
    κ⁻¹ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := inv_mem h

theorem qdf_inv_mem_stab {v : HeightOneSpectrum (𝓞 F)} {κ : GL (Fin n) (E ⊗[F] v.adicCompletion F)}
    (h : κ ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))) : κ⁻¹ ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := inv_mem h

theorem exists_adelic_point_of_local_frames (hS : DecoPtSurj hc n ST SG) (hQ : QOff (F := F) ST SG Q) (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hL : QLift q)
    (p : DecoF E n ST SG Q) (S : Finset Q) :
    ∃ x : UAd hc n, decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = p.deco ∧
      ∀ P ∈ S, (bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x ∈ q.U P := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨ptOf hc n ST SG p.deco, decoOf_ptOf hc n ST SG hS p.deco, fun P hP => absurd hP (Finset.notMem_empty P)⟩
  | insert P S hPS ih =>
    obtain ⟨x, hx, hxS⟩ := ih
    obtain ⟨κ, hκU, hκS, hκ⟩ := hL P _ (hF x p hx P)
    have hput : rll_put n (qv F P.1) κ⁻¹ ∈ K1 hc n ST SG :=
      put_mem_kOne_of_not_over ST SG (fun P' hP' => hQ.off P P' (Or.inl hP'))
        (fun P' hP' => hQ.off P P' (Or.inr hP'))
        (rll_put_mem_UAd hc n (qv F P.1) (qdf_inv_mem_UPts hκU)) (qdf_inv_mem_stab hκS)
    have hputU : rll_put n (qv F P.1) κ⁻¹ ∈ UAd hc n := rll_put_mem_UAd hc n (qv F P.1) (qdf_inv_mem_UPts hκU)
    refine ⟨x * ⟨_, hputU⟩, ?_, ?_⟩
    · show decoOf ST SG ((x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * rll_put n (qv F P.1) κ⁻¹) = _
      rw [decoration_mul_principal hc n ST SG _ hput, hx]
    · intro P' hP'
      show (bc (q.phi P') (qGL n (p.fr P')))⁻¹ * q.at P' ((x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * rll_put n (qv F P.1) κ⁻¹) ∈ q.U P'
      rcases Finset.mem_insert.1 hP' with rfl | hP'
      · rw [qdf_at_put_self, map_inv, hκ, ← mul_assoc, mul_inv_cancel]
        exact one_mem _
      · have hne : qv F P'.1 ≠ qv F P.1 := fun h => hPS (hQ.inj P' P h ▸ hP')
        rw [qdf_at_put_ne q P' _ _ hne]
        exact hxS P' hP'

theorem decoPtSurjF_of (hS : DecoPtSurj hc n ST SG) (hQ : QOff (F := F) ST SG Q) (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hL : QLift q) :
    DecoPtSurjF hc n ST SG Q q := by
  classical
  intro p
  obtain ⟨x, hx, hxS⟩ := exists_adelic_point_of_local_frames hS hQ q hF hL p Finset.univ
  exact ⟨x, hx, fun P => hxS P (Finset.mem_univ P)⟩

end QSurj

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG

section QLiftS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

def qdPair {R : Type} [CommRing R] (k : GL (Fin n) R) : Matrix (Fin n) (Fin n) (R × R) :=
  fun i j => ((k : Matrix (Fin n) (Fin n) R) i j, ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j i)

theorem qdPair_mul_inv {R : Type} [CommRing R] (k : GL (Fin n) R) : qdPair k * qdPair k⁻¹ = 1 := by
  have h1 : (k : Matrix (Fin n) (Fin n) R) * ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 := Units.mul_inv k
  ext i j
  · show (∑ l, ((k : Matrix (Fin n) (Fin n) R) i l, ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l i) *
        (((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l j, ((k⁻¹⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j l)).1 = _
    rw [Prod.fst_sum]
    have := congrArg (fun A : Matrix (Fin n) (Fin n) R => A i j) h1
    simp only [Matrix.mul_apply] at this
    rw [Matrix.one_apply] at this ⊢
    simp only [Prod.fst_mul]
    rw [this]
    split_ifs <;> rfl
  · show (∑ l, ((k : Matrix (Fin n) (Fin n) R) i l, ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l i) *
        (((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l j, ((k⁻¹⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j l)).2 = _
    rw [Prod.snd_sum, inv_inv]
    have := congrArg (fun A : Matrix (Fin n) (Fin n) R => A j i) h1
    simp only [Matrix.mul_apply] at this
    simp only [Prod.snd_mul]
    rw [Matrix.one_apply] at this ⊢
    rw [show (∑ l, ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l i * (k : Matrix (Fin n) (Fin n) R) j l) =
      ∑ l, (k : Matrix (Fin n) (Fin n) R) j l * ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l i from
      Finset.sum_congr rfl fun l _ => mul_comm _ _, this]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]; rfl

def qdPairGL {R : Type} [CommRing R] (k : GL (Fin n) R) : GL (Fin n) (R × R) :=
  ⟨qdPair k, qdPair k⁻¹, qdPair_mul_inv k, by simpa using qdPair_mul_inv k⁻¹⟩

def qdLift (q : QLoc hc n Q Θ) (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F)) : GL (Fin n) (E ⊗[F] (qv F P.1).adicCompletion F) :=
  bc (q.sp P).symm.toRingHom (qdPairGL k)

theorem qdf_sig_symm (q : QLoc hc n Q Θ) (P : Q) (a b : (qv F P.1).adicCompletion F) :
    sigR hc.sig ((qv F P.1).adicCompletion F) ((q.sp P).symm (a, b)) = (q.sp P).symm (b, a) := by
  apply (q.sp P).injective
  rw [q.sp_sig, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rfl

theorem qdLift_fst (q : QLoc hc n Q Θ) (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F)) :
    bc ((RingHom.fst _ _).comp (q.sp P).toRingHom) (qdLift q P k) = k := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show ((q.sp P) ((q.sp P).symm (qdPair k i j))).1 = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem qdf_lift (q : QLoc hc n Q Θ) : QLift q := by
  intro P k hk
  refine ⟨qdLift q P k, ?_, ?_, qdLift_fst q P k⟩
  · show cT (sigR hc.sig ((qv F P.1).adicCompletion F)) ((qdLift q P k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *
        (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) ((qv F P.1).adicCompletion F)) * ((qdLift q P k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) ((qv F P.1).adicCompletion F))
    have hone : (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) ((qv F P.1).adicCompletion F)) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    have hcT : cT (sigR hc.sig ((qv F P.1).adicCompletion F)) ((qdLift q P k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) =
        ((qdLift q P k⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
      refine Matrix.ext fun i j => ?_
      show sigR hc.sig ((qv F P.1).adicCompletion F) ((q.sp P).symm (qdPair k j i)) = (q.sp P).symm (qdPair k⁻¹ i j)
      rw [qdf_sig_symm]
      rfl
    rw [hone, mul_one, hcT]
    rw [← Units.val_mul, qdLift, qdLift, ← map_mul]
    have : qdPairGL k⁻¹ * qdPairGL k = 1 := Units.ext (by
      have h := qdPair_mul_inv k⁻¹
      rw [inv_inv] at h
      exact h)
    rw [this, map_one, Units.val_one]
  · rw [rll_locL_std, Formalism.UG.P.afsplit_stab_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (q.sp P).symm (qdPair k i j) ∈ Formalism.BasicNotions.intV E (qv F P.1)
      rw [q.sp_int, RingEquiv.apply_symm_apply]
      exact ⟨hk.1 i j, hk.2 j i⟩
    · show (q.sp P).symm (qdPair k⁻¹ i j) ∈ Formalism.BasicNotions.intV E (qv F P.1)
      rw [q.sp_int, RingEquiv.apply_symm_apply]
      refine ⟨hk.2 i j, ?_⟩
      have e : (k⁻¹⁻¹ : GL (Fin n) ((qv F P.1).adicCompletion F)) = k := inv_inv k
      show ((↑(k⁻¹⁻¹) : Matrix (Fin n) (Fin n) ((qv F P.1).adicCompletion F)) j i) ∈ _
      rw [e]
      exact hk.1 j i

end QLiftS

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QFr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (Pl E)}

theorem qdf_frame_ratio (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n)
    (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    ∀ y, (p'.fr P).symm (γ (p.fr P y)) ∈ stdAt E n P.1 ↔ y ∈ stdAt E n P.1 := by
  intro y
  have h1 := p'.2 P ((p'.fr P).symm (γ (p.fr P y)))
  have e1 : p'.1.2 P ((p'.fr P).symm (γ (p.fr P y))) = γ (p.fr P y) := LinearEquiv.apply_symm_apply _ _
  rw [e1] at h1
  rw [← h1]
  show γ (p.fr P y) ∈ localization₂ P.1.asIdeal p'.1.1.1.N ↔ _
  have hN' : p'.1.1.1.N = gmap γ p.1.1.1.N := hN
  rw [hN', mem_localization_gmap, LinearEquiv.symm_apply_apply]
  exact p.2 P y

def qdRatio (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n) (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    GLint E n P.1 :=
  ⟨(p.fr P).trans (γ.trans (p'.fr P).symm), fun y => qdf_frame_ratio p p' γ hN P y⟩

end QFr

section QEmpty

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) {K : Type} [Field K]

def QLoc.empty (Θ : LevQFam E K n (∅ : Finset (Pl E))) : QLoc hc n ∅ Θ where
  sp P := absurd P.2 (Finset.notMem_empty _)
  sp_sig P := absurd P.2 (Finset.notMem_empty _)
  sp_alg P := absurd P.2 (Finset.notMem_empty _)
  sp_int P := absurd P.2 (Finset.notMem_empty _)
  sp_P P := absurd P.2 (Finset.notMem_empty _)
  U P := absurd P.2 (Finset.notMem_empty _)
  U_int P := absurd P.2 (Finset.notMem_empty _)
  U_rat P := absurd P.2 (Finset.notMem_empty _)
  U_dense P := absurd P.2 (Finset.notMem_empty _)
  chr P := absurd P.2 (Finset.notMem_empty _)
  chr_rat P := absurd P.2 (Finset.notMem_empty _)

end QEmpty

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QOrb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

theorem qdf_at_rat (q : QLoc hc n Q Θ) (P : Q) (γ : GL (Fin n) E) : q.at P (bc (iA F E) γ) = bc (q.phi P) γ := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rfl

theorem qdf_at_mul (q : QLoc hc n Q Θ) (P : Q) (x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : q.at P (x * y) = q.at P x * q.at P y := by
  show bc _ (bc _ (x * y)) = _
  rw [map_mul, map_mul]

theorem qdf_at_inv (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : q.at P x⁻¹ = (q.at P x)⁻¹ := by
  show bc _ (bc _ x⁻¹) = _
  rw [map_inv, map_inv]

theorem qdf_levUQ_le (H : Subgroup (GLG E n SG)) (q : QLoc hc n Q Θ) : levUQ hc n ST SG Q H q ≤ levU hc n ST SG H := inf_le_left

theorem qdf_levUQ_at (H : Subgroup (GLG E n SG)) (q : QLoc hc n Q Θ) {κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : κ ∈ levUQ hc n ST SG Q H q) (P : Q) : q.at P κ ∈ q.U P :=
  (Subgroup.mem_iInf.1 h.2) P

theorem qdf_ratio_val (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n) (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    (qdRatio p p' γ hN P).1 = (p'.fr P)⁻¹ * γ * p.fr P := rfl

variable (H : Subgroup (GLG E n SG))

theorem qdf_orbit_of_rel (q : QLoc hc n Q Θ) {x x' : UAd hc n} {p p' : DecoF E n ST SG Q}
    (hx : FrOver q x.1 p) (hx' : FrOver q x'.1 p') (γ : URat hc n) (κ : levUQ hc n ST SG Q H q)
    (e : (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
      (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) :
    ∃ a : UF E n × H × Θ.grp, a.1 = ratHom hc n γ ∧ a.2.1 = levRed hc n ST SG H ⟨_, qdf_levUQ_le H q κ.2⟩ ∧ p' = a • p := by
  have hκ : (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ levU hc n ST SG H := qdf_levUQ_le H q κ.2
  have hd : decoOf ST SG (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((ratHom hc n γ, levRed hc n ST SG H ⟨_, hκ⟩) : UF E n × H) • decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [e]; exact rlc_decoOf_sm hc n ST SG H γ ⟨_, hκ⟩ x
  rw [hx.1, hx'.1] at hd
  have hN : p'.deco.1.N = gmap (ratHom hc n γ).1 p.deco.1.N := by rw [hd]; rfl
  have hinj : ∀ a b : GL (Fin n) E, Formalism.UG.glEquiv a = Formalism.UG.glEquiv b → a = b := fun a b h =>
    Units.ext (Matrix.ext_of_mulVec_single fun j => by
      have := congrArg (fun g : Sp E n ≃ₗ[E] Sp E n => g (Pi.single j 1)) h
      simpa [Formalism.UG.glEquiv] using this)
  have hγ : toGLm E n (ratHom hc n γ).1 = (γ : GL (Fin n) E) :=
    hinj _ _ (by rw [glEquiv_toGLm]; rfl)
  have hθ : ∀ P : Q, qdRatio p p' (ratHom hc n γ).1 hN P ∈ (Θ P).H := by
    intro P
    rw [← q.U_rat P]
    have h1 := hx.2 P
    have h2 := hx'.2 P
    have h3 := qdf_levUQ_at H q κ.2 P
    have hx'P : q.at P (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        bc (q.phi P) (γ : GL (Fin n) E) * q.at P x * (q.at P κ)⁻¹ := by
      rw [e, qdf_at_mul, qdf_at_mul, qdf_at_inv, qdf_at_rat]
    have key : bc (q.phi P) (qGL n (qdRatio p p' (ratHom hc n γ).1 hN P).1) =
        ((bc (q.phi P) (qGL n (p'.fr P)))⁻¹ * q.at P x') * q.at P κ * ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x)⁻¹ := by
      rw [qdf_ratio_val]
      simp only [qGL, map_mul, map_inv]
      rw [hγ, hx'P]
      group
    rw [key]
    exact mul_mem (mul_mem h2 h3) (inv_mem h1)
  refine ⟨(ratHom hc n γ, levRed hc n ST SG H ⟨_, hκ⟩, ⟨fun P => qdRatio p p' (ratHom hc n γ).1 hN P,
    (Subgroup.mem_pi _).2 fun P _ => hθ P⟩), rfl, rfl, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hd
  · funext P
    show p'.fr P = (ratHom hc n γ).1 * p.fr P * ((qdRatio p p' (ratHom hc n γ).1 hN P)⁻¹).1
    rw [Subgroup.coe_inv, qdf_ratio_val]
    group

end QOrb

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QCls

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

variable (ST SG Q) in

def FrExists : Prop :=
  ∀ (d : DecoSet E n ST SG) (P : Q), ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ y, f y ∈ d.1.at P.1 ↔ y ∈ stdAt E n P.1

theorem qdf_toGLm_ratHom (γ : URat hc n) : toGLm E n (ratHom hc n γ).1 = (γ : GL (Fin n) E) := by
  simp [toGLm, ratHom, Formalism.UG.glEquiv]

variable (H : Subgroup (GLG E n SG))

theorem qdf_rel_of_orbit (q : QLoc hc n Q Θ) {x x' : UAd hc n} {p : DecoF E n ST SG Q} (a : UF E n × H × Θ.grp)
    (hx : FrOver q x.1 p) (hx' : FrOver q x'.1 (a • p)) :
    ∃ (γ : URat hc n) (κ : levUQ hc n ST SG Q H q), ratHom hc n γ = a.1 ∧
      (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
        (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
  have hd : decoOf ST SG (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((a.1, a.2.1) : UF E n × H) • decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [hx'.1, hx.1]; rfl
  obtain ⟨γ, k, h1, -, e⟩ := rlc_rel_of_orbit hc n ST SG H (a.1, a.2.1) hd
  have hkQ : ∀ P : Q, q.at P (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ q.U P := by
    intro P
    have hke : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      rw [e]; group
    have hA := hx'.2 P
    have hB := hx.2 P
    have hθ : (a.2.2.1 P) ∈ (Θ P).H := (Subgroup.mem_pi _).1 a.2.2.2 P (Set.mem_univ _)
    have hC := (q.U_rat P (a.2.2.1 P)).2 hθ
    have hfr : (a • p).fr P = a.1.1 * p.fr P * ((a.2.2.1 P)⁻¹).1 := rfl
    have hγ : toGLm E n a.1.1 = (γ : GL (Fin n) E) := by rw [← h1]; exact qdf_toGLm_ratHom γ
    have key : q.at P (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        ((bc (q.phi P) (qGL n ((a • p).fr P)))⁻¹ * q.at P x')⁻¹ * bc (q.phi P) (qGL n (a.2.2.1 P).1) *
          ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x) := by
      rw [hke, qdf_at_mul, qdf_at_mul, qdf_at_inv, qdf_at_rat, hfr]
      simp only [qGL, map_mul, map_inv, Subgroup.coe_inv]
      rw [hγ]
      group
    rw [key]
    exact mul_mem (mul_mem (inv_mem hA) hC) hB
  exact ⟨γ, ⟨k.1, k.2, Subgroup.mem_iInf.2 hkQ⟩, h1, e⟩

theorem qdf_over_exists (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hE : FrExists (n := n) ST SG Q) (x : UAd hc n) :
    ∃ p : DecoF E n ST SG Q, FrOver q x.1 p := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : ∀ P : Q, Sp E n ≃ₗ[E] Sp E n,
      ∀ (P : Q) y, f P y ∈ (decoOf ST SG x.1).1.at P.1 ↔ y ∈ stdAt E n P.1 :=
    ⟨fun P => (hE (decoOf ST SG x.1) P).choose, fun P => (hE (decoOf ST SG x.1) P).choose_spec⟩
  let p0 : DecoF E n ST SG Q := ⟨(decoOf ST SG x.1, f), fun P y => hf P y⟩
  have hk := fun P : Q => hF x p0 rfl P
  choose g hg using fun P : Q => q.U_dense P _ (hk P).1 (hk P).2
  refine ⟨⟨(decoOf ST SG x.1, fun P => f P * (g P).1), fun P y => ?_⟩, rfl, fun P => ?_⟩
  · show f P ((g P).1 y) ∈ _ ↔ _
    rw [hf P]
    exact (g P).2 y
  · show (Formalism.UG.bc (q.phi P) (qGL n (f P * (g P).1)))⁻¹ * q.at P x.1 ∈ q.U P
    rw [show qGL n (f P * (g P).1) = qGL n (f P) * qGL n (g P).1 from map_mul _ _ _, map_mul, _root_.mul_inv_rev,
      mul_assoc]
    exact hg P

end QCls

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QRec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}
variable (H : Subgroup (GLG E n SG))

theorem qdf_ptOfF_spec (q : QLoc hc n Q Θ) (hSF : DecoPtSurjF hc n ST SG Q q) (p : DecoF E n ST SG Q) :
    FrOver q (ptOfF hc n ST SG Q q p).1 p := by
  unfold ptOfF
  rw [dif_pos (hSF p)]
  exact (hSF p).choose_spec

theorem qdf_levUQ_le_UAd (q : QLoc hc n Q Θ) : levUQ hc n ST SG Q H q ≤ UAd hc n := by
  unfold levUQ
  exact inf_le_left.trans (levU_le_UAd ..)

theorem qdf_mk_eq (q : QLoc hc n Q Θ) {x y : UAd hc n} (γ : URat hc n) (k : levUQ hc n ST SG Q H q)
    (e : (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) *
        (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) :
    (Quotient.mk'' y : Formalism.L2.DIV.Cl hc (1 : Matrix (Fin n) (Fin n) E) (levUQ hc n ST SG Q H q)) = Quotient.mk'' x := by
  have hk : ((k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))⁻¹ ∈ UAd hc n :=
    qdf_levUQ_le_UAd H q (Subgroup.inv_mem _ k.2)
  refine Quotient.sound (DoubleCoset.rel_iff.2 ⟨(Formalism.L2.DIV.ratEl γ : UAd hc n), (Formalism.L2.DIV.ratEl γ).2, ⟨_, hk⟩,
    Subgroup.mem_subgroupOf.2 (Subgroup.inv_mem _ k.2), ?_⟩)
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact e

def qdStab (p : DecoF E n ST SG Q) : MulAction.stabilizer (UF E n × H × Θ.grp) p →* URat hc n :=
  (ratEquiv hc n).symm.toMonoidHom.comp ((MonoidHom.fst (UF E n) (H × Θ.grp)).comp (Subgroup.subtype _))

theorem qdf_ratHom_stab (p : DecoF E n ST SG Q) (a : MulAction.stabilizer (UF E n × H × Θ.grp) p) :
    ratHom hc n (qdStab H p a) = a.1.1 := by
  show ratEquiv hc n ((ratEquiv hc n).symm a.1.1) = a.1.1
  exact MulEquiv.apply_symm_apply _ _

theorem qdf_stab_deco (p : DecoF E n ST SG Q) (a : MulAction.stabilizer (UF E n × H × Θ.grp) p) :
    ((a.1.1, a.1.2.1) : UF E n × H) ∈ MulAction.stabilizer (UF E n × H) p.deco := by
  have h := congrArg DecoF.deco (MulAction.mem_stabilizer_iff.1 a.2)
  exact MulAction.mem_stabilizer_iff.2 h

theorem qdf_stab_fr (p : DecoF E n ST SG Q) (a : MulAction.stabilizer (UF E n × H × Θ.grp) p) (P : Q) :
    (a.1.2.2.1 P).1 = (p.fr P)⁻¹ * a.1.1.1 * p.fr P := by
  have h : (a.1 • p).fr P = p.fr P := congrArg (fun x : DecoF E n ST SG Q => x.fr P) (MulAction.mem_stabilizer_iff.1 a.2)
  change a.1.1.1 * p.fr P * ((a.1.2.2.1 P).1)⁻¹ = p.fr P at h
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

variable {H}

def recClsF (q : QLoc hc n Q Θ) (hSF : DecoPtSurjF hc n ST SG Q q) (hF : FrLat ST SG q) (hE : FrExists (n := n) ST SG Q)
    (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q) (hs : ∀ c, (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q H Θ) = c) :
    RecClsF hc n ST SG Q H q s where
  y c := ptOfF hc n ST SG Q q (s c)
  y_bij := by
    constructor
    · intro c c' h
      have hr := Quotient.exact' h
      obtain ⟨h0, hh, k, hk, e⟩ := DoubleCoset.rel_iff.1 hr
      obtain ⟨γ, hγ⟩ := Formalism.L2.DIV.ratEl_surjective (⟨h0, hh⟩ : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E))
      have hh' : ((h0 : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) :=
        (congrArg (fun z : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E) =>
          ((z : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) hγ).symm
      have hk' : ((k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ ∈ levUQ hc n ST SG Q H q :=
        Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hk)
      have e' : ((ptOfF hc n ST SG Q q (s c') : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
          Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            (((⟨_, hk'⟩ : levUQ hc n ST SG Q H q) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))⁻¹ := by
        have e2 := congrArg (fun z : UAd hc n => (z : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) e
        simp only [Subgroup.coe_mul] at e2
        rw [e2, hh', inv_inv]
      obtain ⟨a, -, -, ha⟩ := qdf_orbit_of_rel H q (qdf_ptOfF_spec q hSF (s c)) (qdf_ptOfF_spec q hSF (s c')) γ ⟨_, hk'⟩ e'
      rw [← hs c, ← hs c']
      exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨a⁻¹, by show a⁻¹ • s c' = s c; rw [ha, inv_smul_smul]⟩)
    · intro Qc
      induction Qc using Quotient.inductionOn' with
      | h x =>
        obtain ⟨p, hp⟩ := qdf_over_exists q hF hE x
        refine ⟨Quotient.mk'' p, ?_⟩
        obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.1 (Quotient.exact (hs (Quotient.mk'' p)))
        have ha' : a • p = s (Quotient.mk'' p) := ha
        have hx' : FrOver q (ptOfF hc n ST SG Q q (s (Quotient.mk'' p))).1 (a • p) := by
          rw [ha']; exact qdf_ptOfF_spec q hSF _
        obtain ⟨γ, κ, -, e⟩ := qdf_rel_of_orbit H q a hp hx'
        exact (qdf_mk_eq H q γ κ e).symm
  y_lat c x := by
    have h := decoRaw_carries hc n ST SG (ptOfF hc n ST SG Q q (s c)).2 x
    rw [← rlc_decoOf_val hc n ST SG (ptOfF hc n ST SG Q q (s c)).2, (qdf_ptOfF_spec q hSF (s c)).1] at h
    exact h
  stabI c := qdStab H (s c)
  stabI_inj c := by
    intro a b hab
    have h1 : a.1.1 = b.1.1 := by rw [← qdf_ratHom_stab (hc := hc) H (s c) a, ← qdf_ratHom_stab (hc := hc) H (s c) b, hab]
    have ha := qdf_stab_deco H (s c) a
    have hb := qdf_stab_deco H (s c) b
    have hab' : ((a.1.1, (a.1.2.1 : GLG E n SG)) : UF E n × GLG E n SG) • (s c).deco = (s c).deco := ha
    have hbb' : ((b.1.1, (b.1.2.1 : GLG E n SG)) : UF E n × GLG E n SG) • (s c).deco = (s c).deco := hb
    have h2 := DecoSet.stab_fst_injective (s c).deco hab' hbb' h1
    have h3 : a.1.2.2 = b.1.2.2 := by
      apply Subtype.ext
      funext P
      apply Subtype.ext
      rw [qdf_stab_fr H (s c) a P, qdf_stab_fr H (s c) b P, h1]
    exact Subtype.ext (Prod.ext h1 (Prod.ext (Subtype.ext (congrArg Prod.snd h2)) h3))
  stabI_range c γ hγ := by
    constructor
    · rintro ⟨a, ha⟩
      have hx := qdf_ptOfF_spec q hSF (s c)
      have hx' : FrOver q (ptOfF hc n ST SG Q q (s c)).1 (a.1 • s c) := by rw [a.2]; exact hx
      obtain ⟨γ', κ, h1, e⟩ := qdf_rel_of_orbit H q a.1 hx hx'
      have hγ' : γ' = ⟨γ, hγ⟩ := by
        rw [← ha]
        exact (ratHom_bijective hc n).1 (h1.trans (qdf_ratHom_stab (hc := hc) H (s c) a).symm)
      refine ⟨κ.1, κ.2, ?_⟩
      show ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * κ.1 *
        ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ = _
      have e' : Formalism.UG.bc (iA F E) (γ' : GL (Fin n) E) = ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          κ.1 * ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ :=
        eq_mul_inv_of_mul_eq (eq_mul_inv_iff_mul_eq.1 e).symm
      rw [← e', hγ']
    · rintro ⟨k, hk, e⟩
      have e' : ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * k *
          ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ =
          Formalism.UG.bc (iA F E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) E) := e
      have e2 : ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
          Formalism.UG.bc (iA F E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) E) *
            ((ptOfF hc n ST SG Q q (s c) : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            ((⟨k, hk⟩ : levUQ hc n ST SG Q H q) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
        rw [← e']; group
      obtain ⟨a, ha1, -, ha⟩ := qdf_orbit_of_rel H q (qdf_ptOfF_spec q hSF (s c)) (qdf_ptOfF_spec q hSF (s c)) ⟨γ, hγ⟩ ⟨k, hk⟩ e2
      refine ⟨⟨a, ha.symm⟩, ?_⟩
      apply (ratHom_bijective hc n).1
      rw [qdf_ratHom_stab (hc := hc) H (s c) ⟨a, ha.symm⟩, ha1]
  stabI_lat c a x := by
    have h := stabRat_lat hc n ST SG H (s c).deco ⟨_, qdf_stab_deco H (s c) a⟩ x
    have e : stabRat hc n ST SG H (s c).deco ⟨_, qdf_stab_deco H (s c) a⟩ = qdStab H (s c) a :=
      (ratHom_bijective hc n).1 ((rlc_ratHom_stabRat hc n ST SG H _ _).trans (qdf_ratHom_stab (hc := hc) H (s c) a).symm)
    rw [e] at h
    exact h

end QRec

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl)

section QTop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}
  {H : Subgroup (GLG E n SG)}

end QTop

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV

section L3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem mem_localization_of_smul_mem'₂ (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) {s : 𝓞 E}
    (hs : s ∉ P.asIdeal) {w : Sp E n} (h : s • w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
  obtain ⟨s', hs', h'⟩ := (mem_locP P N _).1 h
  refine (mem_locP P N w).2 ⟨s' * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs' hs, ?_⟩
  rwa [mul_smul]

theorem frame_exists (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ z, f z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n) := by
  obtain ⟨β, hβN, hβI⟩ := exists_locBasis P hN
  refine ⟨β.equivFun.symm, fun z => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [mem_localization_standardLattice]
    intro i
    have := hβI _ h i
    rwa [Module.Basis.equivFun_symm_apply, Module.Basis.repr_sum_self] at this
  · rw [mem_localization_standardLattice] at h
    rw [Module.Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, s, hs, hrs⟩ := h i
    apply mem_localization_of_smul_mem'₂ P N hs
    have e : s • (z i • β i) = r • β i := by
      rw [← algebraMap_smul E s, ← algebraMap_smul E r, smul_smul, hrs]
    rw [e]
    exact Submodule.smul_mem _ r (hβN i)

end L3

section Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

end Mat

section Unit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

end Unit

section Bwd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

end Bwd

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

end Cong

end DetChrL

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

theorem qdf_frExists : FrExists (n := n) ST SG Q := fun d P => DetChrL.frame_exists P.1 d.2.lat

abbrev qPi (q : QLoc hc n Q Θ) (P : Q) : E ⊗[F] Formalism.L2.Herm.Af F →+* (qv F P.1).adicCompletion F :=
  ((RingHom.fst _ _).comp (q.sp P).toRingHom).comp (prV (E := E) (qv F P.1))

theorem qdf_at_val (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    ((q.at P x : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) = (x : Matrix (Fin n) (Fin n) _).map (qPi q P) := rfl


theorem qdf_phi_int (q : QLoc hc n Q Θ) (P : Q) (r : 𝓞 E) : q.phi P (r : E) ∈ (qv F P.1).adicCompletionIntegers F := by
  have h : Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) (r : E) ∈ Formalism.BasicNotions.intV E (qv F P.1) :=
    Subring.subset_closure (Or.inl ⟨⟨(r : E), r, rfl⟩, rfl⟩)
  exact ((q.sp_int P _).1 h).1

theorem qdf_pi_int (q : QLoc hc n Q Θ) (P : Q) {a : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E) :
    qPi q P a ∈ (qv F P.1).adicCompletionIntegers F := by
  have hle : Formalism.L2.Herm.intAf F E ≤
      (Formalism.BasicNotions.intV E (qv F P.1)).comap (Formalism.UG.prV (E := E) (qv F P.1)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · refine Subring.mem_comap.2 (Subring.subset_closure (Or.inl ⟨x, ?_⟩))
      simp [Formalism.UG.prV]
    · have hy : ∀ v, (y : Formalism.L2.Herm.Af F) v ∈ v.adicCompletionIntegers F := y.2
      refine Subring.mem_comap.2 (Subring.subset_closure (Or.inr ⟨⟨(y : Formalism.L2.Herm.Af F) (qv F P.1), hy _⟩, ?_⟩))
      simp [Formalism.UG.prV] <;> rfl
  exact ((q.sp_int P _).1 (hle ha)).1

theorem qdf_phi_unit (q : QLoc hc n Q Θ) (P : Q) {s : 𝓞 E} (hs : s ∉ P.1.asIdeal) :
    q.phi P (s : E) ≠ 0 ∧ (q.phi P (s : E))⁻¹ ∈ (qv F P.1).adicCompletionIntegers F := by
  have h1 : Valued.v (q.phi P (s : E)) ≤ 1 := qdf_phi_int q P s
  have h2 : ¬ Valued.v (q.phi P (s : E)) < 1 := fun h => hs ((q.sp_P P s).1 h)
  have hv : Valued.v (q.phi P (s : E)) = 1 := le_antisymm h1 (not_lt.1 h2)
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, map_zero] at hv
    exact zero_ne_one hv
  · show Valued.v (q.phi P (s : E))⁻¹ ≤ 1
    rw [map_inv₀, hv, inv_one]

theorem qdf_phi_intAt (q : QLoc hc n Q Θ) (P : Q) {a : E} (h : IntAt P.1 a) : q.phi P a ∈ (qv F P.1).adicCompletionIntegers F := by
  obtain ⟨r, s, hs, h⟩ := h
  have hu := qdf_phi_unit q P hs
  have hm : q.phi P (s : E) * q.phi P a = q.phi P (r : E) := by
    rw [← map_mul]
    exact congrArg (q.phi P) h
  have ha : q.phi P a = q.phi P (r : E) * (q.phi P (s : E))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hu.1, mul_comm]
    exact hm
  rw [ha]
  exact mul_mem (qdf_phi_int q P r) hu.2


theorem qdf_frLat (q : QLoc hc n Q Θ) : FrLat ST SG q := by
  intro x p hx P
  have hN : p.deco.1.N = Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n) := by
    rw [← hx, rlc_decoOf_val hc n ST SG x.2]; rfl
  set fr := p.fr P with hfr

  have hfrN : ∀ w ∈ p.deco.1.N, ∀ i, q.phi P ((fr.symm w) i) ∈ (qv F P.1).adicCompletionIntegers F := by
    intro w hw i
    have h1 : fr (fr.symm w) ∈ p.deco.1.at P.1 := by
      rw [LinearEquiv.apply_symm_apply]
      exact (mem_locP P.1 _ w).2 ⟨1, P.1.isPrime.one_notMem, by rw [one_smul]; exact hw⟩
    have h2 : fr.symm w ∈ stdAt E n P.1 := (p.2 P (fr.symm w)).1 h1
    exact qdf_phi_intAt q P ((mem_localization_standardLattice P.1 _).1 h2 i)
  have hFinv : ((bc (q.phi P) (qGL n fr))⁻¹ : GL (Fin n) _) = bc (q.phi P) (qGL n fr.symm) := by
    rw [← map_inv]; congr 1
  constructor
  ·
    set xm : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := x.1 with hxm
    have key : ∀ z ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n)), ∀ i,
        ((((bc (q.phi P) (qGL n fr))⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => qPi q P (z k))) i ∈
          (qv F P.1).adicCompletionIntegers F := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨w, hw, rfl⟩ := hz
        intro i
        rw [hFinv]
        have e1 : ((bc (q.phi P) (qGL n fr.symm) : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => qPi q P (iA F E (w k))) =
            fun k => q.phi P ((fr.symm w) k) := by
          funext k
          rw [← toGLm_mulVec fr.symm w]
          exact (RingHom.map_mulVec (q.phi P) _ w k).symm
        rw [e1]
        exact hfrN w (by rw [hN]; exact hw) i
      | zero =>
        intro i
        have e0 : (fun k => qPi q P ((0 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) k)) = 0 := by funext k; simp
        rw [e0, Matrix.mulVec_zero]
        exact zero_mem _
      | add z1 z2 _ _ h1 h2 =>
        intro i
        have e2 : (fun k => qPi q P ((z1 + z2) k)) = (fun k => qPi q P (z1 k)) + (fun k => qPi q P (z2 k)) := by
          funext k; simp
        rw [e2, Matrix.mulVec_add]
        exact add_mem (h1 i) (h2 i)
      | smul a z1 _ h1 =>
        intro i
        have e2 : (fun k => qPi q P ((a • z1) k)) = qPi q P (a : E ⊗[F] Formalism.L2.Herm.Af F) • (fun k => qPi q P (z1 k)) := by
          funext k
          show qPi q P ((a : E ⊗[F] Formalism.L2.Herm.Af F) * z1 k) = _
          rw [map_mul]; rfl
        rw [e2, Matrix.mulVec_smul]
        exact mul_mem (qdf_pi_int q P a.2) (h1 i)
    intro i j
    have hz : (fun k => (xm : Matrix (Fin n) (Fin n) _) k j) ∈ Formalism.L2.Herm.hatL (F := F)
        (Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n)) := by
      refine (Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n)
        (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top xm _).2 ?_
      have e3 : (((xm⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          fun k => (xm : Matrix (Fin n) (Fin n) _) k j) = fun k => iA F E ((Pi.single j (1 : E) : Sp E n) k) := by
        have : (fun k => (xm : Matrix (Fin n) (Fin n) _) k j) =
            (xm : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ Pi.single j (1 : E ⊗[F] Formalism.L2.Herm.Af F) := by
          funext k; rw [Matrix.mulVec_single_one]; rfl
        rw [this, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        funext k
        by_cases hk : k = j
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      rw [e3]
      exact Submodule.subset_span ⟨Pi.single j 1, by
        have := single_mem_stdLat (E := E) (n := n) j 1
        simpa using this, rfl⟩
    have := key _ hz i
    have e7 : ((((bc (q.phi P) (qGL n fr))⁻¹ * q.at P xm : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j) =
        ((((bc (q.phi P) (qGL n fr))⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          fun k => qPi q P ((xm : Matrix (Fin n) (Fin n) _) k j)) i := by
      rw [Units.val_mul, qdf_at_val]; rfl
    rw [e7]
    exact this
  ·
    intro i j
    have e0 : (((bc (q.phi P) (qGL n fr))⁻¹ * q.at P x)⁻¹ : GL (Fin n) _) = (q.at P x)⁻¹ * bc (q.phi P) (qGL n fr) := by
      rw [_root_.mul_inv_rev, inv_inv]
    rw [e0]
    have hcol : fr (Pi.single j 1) ∈ p.deco.1.at P.1 :=
      (p.2 P (Pi.single j 1)).2 ((mem_localization_standardLattice P.1 _).2 fun k => ⟨if k = j then 1 else 0, 1, P.1.isPrime.one_notMem, by
        by_cases hk : k = j <;> simp [Pi.single_apply, hk]⟩)
    obtain ⟨s, hs, hsN⟩ := (mem_locP P.1 _ _).1 hcol
    rw [hN] at hsN
    have hpull := (mem_globLat x.1 (s • fr (Pi.single j 1))).1 hsN
    obtain ⟨hne, hinv⟩ := qdf_phi_unit q P hs
    have e4 : ((((q.at P x)⁻¹ * bc (q.phi P) (qGL n fr) : GL (Fin n) _)) : Matrix (Fin n) (Fin n) _) i j =
        (q.phi P (s : E))⁻¹ * qPi q P (pullV x.1 (s • fr (Pi.single j 1)) i) := by
      have e5 : qPi q P (pullV x.1 (s • fr (Pi.single j 1)) i) =
          ((((q.at P x)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ fun k => q.phi P ((s • fr (Pi.single j 1)) k)) i := by
        unfold pullV
        rw [RingHom.map_mulVec, ← qdf_at_inv, qdf_at_val]
        rfl
      rw [e5]
      have e6 : (fun k => q.phi P ((s • fr (Pi.single j 1)) k)) = q.phi P (s : E) • fun k => q.phi P ((fr (Pi.single j 1)) k) := by
        funext k
        simp [Submodule.smul_def, Algebra.smul_def]
      rw [e6, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul, Units.val_mul,
        Matrix.mul_apply]
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
    rw [e4]
    exact mul_mem hinv (qdf_pi_int q P (hpull i))

variable {H : Subgroup (GLG E n SG)}

end QLat

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QExact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

def FrExact (q : QLoc hc n Q Θ) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (p : DecoF E n ST SG Q) : Prop :=
  decoOf ST SG x = p.deco ∧ ∀ P : Q, q.at P x = bc (q.phi P) (qGL n (p.fr P))

theorem FrExact.over {q : QLoc hc n Q Θ} {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {p : DecoF E n ST SG Q} (h : FrExact q x p) :
    FrOver q x p := by
  refine ⟨h.1, fun P => ?_⟩
  rw [h.2 P, inv_mul_cancel]
  exact (q.U P).one_mem

variable {H : Subgroup (GLG E n SG)}

def recClsFy (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hE : FrExists (n := n) ST SG Q)
    (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q) (hs : ∀ c, (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q H Θ) = c)
    (y : DecoFCl (K := K) n ST SG Q H Θ → UAd hc n) (hy : ∀ c, FrOver q (y c).1 (s c)) :
    RecClsF hc n ST SG Q H q s where
  y c := y c
  y_bij := by
    constructor
    · intro c c' h
      have hr := Quotient.exact' h
      obtain ⟨h0, hh, k, hk, e⟩ := DoubleCoset.rel_iff.1 hr
      obtain ⟨γ, hγ⟩ := Formalism.L2.DIV.ratEl_surjective (⟨h0, hh⟩ : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E))
      have hh' : ((h0 : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) :=
        (congrArg (fun z : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E) =>
          ((z : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) hγ).symm
      have hk' : ((k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ ∈ levUQ hc n ST SG Q H q :=
        Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hk)
      have e' : ((y c' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
          Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            (((⟨_, hk'⟩ : levUQ hc n ST SG Q H q) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))⁻¹ := by
        have e2 := congrArg (fun z : UAd hc n => (z : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) e
        simp only [Subgroup.coe_mul] at e2
        rw [e2, hh', inv_inv]
      obtain ⟨a, -, -, ha⟩ := qdf_orbit_of_rel H q (hy c) (hy c') γ ⟨_, hk'⟩ e'
      rw [← hs c, ← hs c']
      exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨a⁻¹, by show a⁻¹ • s c' = s c; rw [ha, inv_smul_smul]⟩)
    · intro Qc
      induction Qc using Quotient.inductionOn' with
      | h x =>
        obtain ⟨p, hp⟩ := qdf_over_exists q hF hE x
        refine ⟨Quotient.mk'' p, ?_⟩
        obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.1 (Quotient.exact (hs (Quotient.mk'' p)))
        have ha' : a • p = s (Quotient.mk'' p) := ha
        have hx' : FrOver q (y (Quotient.mk'' p)).1 (a • p) := by
          rw [ha']; exact hy _
        obtain ⟨γ, κ, -, e⟩ := qdf_rel_of_orbit H q a hp hx'
        exact (qdf_mk_eq H q γ κ e).symm
  y_lat c x := by
    have h := decoRaw_carries hc n ST SG (y c).2 x
    rw [← rlc_decoOf_val hc n ST SG (y c).2, (hy c).1] at h
    exact h
  stabI c := qdStab H (s c)
  stabI_inj c := by
    intro a b hab
    have h1 : a.1.1 = b.1.1 := by rw [← qdf_ratHom_stab (hc := hc) H (s c) a, ← qdf_ratHom_stab (hc := hc) H (s c) b, hab]
    have ha := qdf_stab_deco H (s c) a
    have hb := qdf_stab_deco H (s c) b
    have hab' : ((a.1.1, (a.1.2.1 : GLG E n SG)) : UF E n × GLG E n SG) • (s c).deco = (s c).deco := ha
    have hbb' : ((b.1.1, (b.1.2.1 : GLG E n SG)) : UF E n × GLG E n SG) • (s c).deco = (s c).deco := hb
    have h2 := DecoSet.stab_fst_injective (s c).deco hab' hbb' h1
    have h3 : a.1.2.2 = b.1.2.2 := by
      apply Subtype.ext
      funext P
      apply Subtype.ext
      rw [qdf_stab_fr H (s c) a P, qdf_stab_fr H (s c) b P, h1]
    exact Subtype.ext (Prod.ext h1 (Prod.ext (Subtype.ext (congrArg Prod.snd h2)) h3))
  stabI_range c γ hγ := by
    constructor
    · rintro ⟨a, ha⟩
      have hx := hy c
      have hx' : FrOver q (y c).1 (a.1 • s c) := by rw [a.2]; exact hx
      obtain ⟨γ', κ, h1, e⟩ := qdf_rel_of_orbit H q a.1 hx hx'
      have hγ' : γ' = ⟨γ, hγ⟩ := by
        rw [← ha]
        exact (ratHom_bijective hc n).1 (h1.trans (qdf_ratHom_stab (hc := hc) H (s c) a).symm)
      refine ⟨κ.1, κ.2, ?_⟩
      show ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * κ.1 *
        ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ = _
      have e' : Formalism.UG.bc (iA F E) (γ' : GL (Fin n) E) = ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          κ.1 * ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ :=
        eq_mul_inv_of_mul_eq (eq_mul_inv_iff_mul_eq.1 e).symm
      rw [← e', hγ']
    · rintro ⟨k, hk, e⟩
      have e' : ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * k *
          ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ =
          Formalism.UG.bc (iA F E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) E) := e
      have e2 : ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
          Formalism.UG.bc (iA F E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) E) *
            ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            ((⟨k, hk⟩ : levUQ hc n ST SG Q H q) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
        rw [← e']; group
      obtain ⟨a, ha1, -, ha⟩ := qdf_orbit_of_rel H q (hy c) (hy c) ⟨γ, hγ⟩ ⟨k, hk⟩ e2
      refine ⟨⟨a, ha.symm⟩, ?_⟩
      apply (ratHom_bijective hc n).1
      rw [qdf_ratHom_stab (hc := hc) H (s c) ⟨a, ha.symm⟩, ha1]
  stabI_lat c a x := by
    have h := stabRat_lat hc n ST SG H (s c).deco ⟨_, qdf_stab_deco H (s c) a⟩ x
    have e : stabRat hc n ST SG H (s c).deco ⟨_, qdf_stab_deco H (s c) a⟩ = qdStab H (s c) a :=
      (ratHom_bijective hc n).1 ((rlc_ratHom_stabRat hc n ST SG H _ _).trans (qdf_ratHom_stab (hc := hc) H (s c) a).symm)
    rw [e] at h
    exact h

end QExact

end Formalism.L2.Col
end
end
