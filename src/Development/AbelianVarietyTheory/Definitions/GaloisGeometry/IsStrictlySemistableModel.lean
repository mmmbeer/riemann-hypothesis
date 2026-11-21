import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubsingletonObjOfIsEmpty

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

section Transfer

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem eq_one_of_isIso_codiag {S : Scheme.{0}} (pt : S) {m : ℕ}
    (h : IsIso (Sigma.desc (fun _ : Fin m => 𝟙 S) : ∐ (fun _ : Fin m => S) ⟶ S)) : m = 1 := by
  rcases Nat.lt_trichotomy m 1 with hm | hm | hm
  · have hm0 : m = 0 := by omega
    subst hm0
    have f : S ⟶ (∅ : Scheme.{0}) :=
      inv (Sigma.desc (fun _ : Fin 0 => 𝟙 S)) ≫ Sigma.desc (fun j : Fin 0 => j.elim0)
    exact (IsEmpty.false (f pt)).elim
  · exact hm
  · exfalso
    let i : Fin m := ⟨0, by omega⟩
    let j : Fin m := ⟨1, hm⟩
    have hij : Sigma.ι (fun _ : Fin m => S) i = Sigma.ι (fun _ : Fin m => S) j :=
      (cancel_mono (Sigma.desc (fun _ : Fin m => 𝟙 S))).1 (by simp)
    have hp : Sigma.ι (fun _ : Fin m => S) i pt = Sigma.ι (fun _ : Fin m => S) j pt := by rw [hij]
    have := congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin m => S) i j pt pt).mp hp)
    simp [i, j] at this

end Transfer

section Semistable

variable (O : Type) [CommRing O] (ϖ : O) (m r : ℕ)

abbrev ssModel : Type :=
  MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
      MvPolynomial.C ϖ}

theorem isStrictlySemistable_model (h1 : 1 ≤ r) (h2 : r ≤ m) :
    IsStrictlySemistable ϖ (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))) := by
  intro x
  refine ⟨⊤, isAffineOpen_top _, trivial, m, r, h1, h2, (Scheme.ΓSpecIso (CommRingCat.of (ssModel O ϖ m r))).inv.hom,
    RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _), ?_⟩
  have h : (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))).appTop =
      (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))).appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE _
  rw [← h, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

example : IsStrictlySemistable (2 : ℤ) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ssModel ℤ 2 2 2)))) :=
  isStrictlySemistable_model ℤ 2 2 2 (by norm_num) le_rfl

end Semistable

section MuTest

example : (-1 : ℤˣ) ∈ rootsOfUnity 2 ℤ := by
  rw [mem_rootsOfUnity]; decide

end MuTest

end GlobalTheory.Et

end
