import Development.EtaleCohomology.EtaleSheaves.LeafKumCut

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.H1MultiplicativeGroup

structure Cov (A : Type) [CommRing A] where

  B : Type
  [cr : CommRing B]
  [alg : Algebra A B]
  [et : Algebra.Etale A B]
  [ff : Module.FaithfullyFlat A B]

attribute [instance] Cov.cr Cov.alg Cov.et Cov.ff

def kerH (A : Type) [CommRing A] (U : Cov A) : AddSubgroup (H ℤ (sp A) Gm 1) :=
  (pull ℤ (spMap (algebraMap A U.B)) Gm 1).ker

def kerP (A : Type) [CommRing A] (U : Cov A) : AddSubgroup (Additive (CommRing.Pic A)) :=
  (CommRing.Pic.mapAlgebra A U.B).toAdditive.ker

def LeafKill : Prop := Hyps → ∀ (A : Type) [CommRing A] (x : H ℤ (sp A) Gm 1), ∃ U : Cov A, x ∈ kerH A U

def LeafTriv : Prop := ∀ (A : Type) [CommRing A] (c : Additive (CommRing.Pic A)), ∃ U : Cov A, c ∈ kerP A U

def LeafRefine : Prop := ∀ (A : Type) [CommRing A] (U V : Cov A), ∃ W : Cov A,
  Nonempty (U.B →ₐ[A] W.B) ∧ Nonempty (V.B →ₐ[A] W.B)

def LeafDesc : Prop := Hyps → ∀ (A : Type) [CommRing A], ∃ e : ∀ U : Cov A, kerH A U ≃+ kerP A U,
  ∀ (U V : Cov A) (_g : U.B →ₐ[A] V.B) (x : H ℤ (sp A) Gm 1) (hU : x ∈ kerH A U) (hV : x ∈ kerH A V),
    (e U ⟨x, hU⟩ : Additive (CommRing.Pic A)) = e V ⟨x, hV⟩

theorem kerH_mono (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) : kerH A U ≤ kerH A V := by
  intro x hx
  simp only [kerH, AddMonoidHom.mem_ker] at hx ⊢
  have h : spMap (algebraMap A V.B) = spMap (g : U.B →+* V.B) ≫ spMap (algebraMap A U.B) := by
    simp only [spMap]
    rw [← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
  rw [h, pull_comp, hx, map_zero]

theorem goal_of (hK : LeafKill) (hT : LeafTriv) (hR : LeafRefine) (hD : LeafDesc) : LateralTheory.E.LeafKumCut.EtaleFirstCohomologyMultiplicativeGroupPicard := by
  intro hH A _
  obtain ⟨e, he⟩ := hD hH A
  choose U hU using hK hH A
  have key : ∀ (x : H ℤ (sp A) Gm 1) (V : Cov A) (hV : x ∈ kerH A V),
      (e V ⟨x, hV⟩ : Additive (CommRing.Pic A)) = e (U x) ⟨x, hU x⟩ := by
    intro x V hV
    obtain ⟨W, ⟨g1⟩, ⟨g2⟩⟩ := hR A V (U x)
    rw [he V W g1 x hV (kerH_mono A V W g1 hV), he (U x) W g2 x (hU x) (kerH_mono A (U x) W g2 (hU x))]
  let f : H ℤ (sp A) Gm 1 →+ Additive (CommRing.Pic A) :=
    { toFun := fun x => e (U x) ⟨x, hU x⟩
      map_zero' := by
        have h0 : (⟨0, hU 0⟩ : kerH A (U 0)) = 0 := rfl
        rw [h0, map_zero]
        rfl
      map_add' := fun x y => by
        show (e (U (x + y)) ⟨x + y, hU _⟩ : Additive (CommRing.Pic A)) = e (U x) ⟨x, hU x⟩ + e (U y) ⟨y, hU y⟩
        obtain ⟨W, ⟨g1⟩, ⟨g2⟩⟩ := hR A (U x) (U y)
        have hx := kerH_mono A _ W g1 (hU x)
        have hy := kerH_mono A _ W g2 (hU y)
        rw [← key x W hx, ← key y W hy, ← key (x + y) W (add_mem hx hy), ← AddSubgroup.coe_add, ← map_add]
        rfl }
  refine ⟨AddEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro x y h
    obtain ⟨W, ⟨g1⟩, ⟨g2⟩⟩ := hR A (U x) (U y)
    have hx := kerH_mono A _ W g1 (hU x)
    have hy := kerH_mono A _ W g2 (hU y)
    have h' : e W ⟨x, hx⟩ = e W ⟨y, hy⟩ := Subtype.ext (by rw [key x W hx, key y W hy]; exact h)
    exact congrArg Subtype.val ((e W).injective h')
  · intro c
    obtain ⟨V, hV⟩ := hT A c
    obtain ⟨⟨x, hx⟩, hxe⟩ := (e V).surjective ⟨c, hV⟩
    refine ⟨x, ?_⟩
    show (e (U x) ⟨x, hU x⟩ : Additive (CommRing.Pic A)) = c
    rw [← key x V hx, hxe]

end LateralTheory.E.H1MultiplicativeGroup
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H1MultiplicativeGroup
open scoped TensorProduct

namespace LateralTheory.E.LeafDescCut

def d0 (A : Type) [CommRing A] (U : Cov A) : U.B →ₐ[A] U.B ⊗[A] U.B := Algebra.TensorProduct.includeRight

def d1 (A : Type) [CommRing A] (U : Cov A) : U.B →ₐ[A] U.B ⊗[A] U.B := Algebra.TensorProduct.includeLeft

def p12 (A : Type) [CommRing A] (U : Cov A) : U.B ⊗[A] U.B →ₐ[A] U.B ⊗[A] (U.B ⊗[A] U.B) :=
  Algebra.TensorProduct.map (AlgHom.id A U.B) Algebra.TensorProduct.includeLeft

def p13 (A : Type) [CommRing A] (U : Cov A) : U.B ⊗[A] U.B →ₐ[A] U.B ⊗[A] (U.B ⊗[A] U.B) :=
  Algebra.TensorProduct.map (AlgHom.id A U.B) Algebra.TensorProduct.includeRight

def p23 (A : Type) [CommRing A] (U : Cov A) : U.B ⊗[A] U.B →ₐ[A] U.B ⊗[A] (U.B ⊗[A] U.B) :=
  Algebra.TensorProduct.includeRight

def cob1 (A : Type) [CommRing A] (U : Cov A) : (U.B ⊗[A] U.B)ˣ →* (U.B ⊗[A] (U.B ⊗[A] U.B))ˣ :=
  Units.map (p13 A U : U.B ⊗[A] U.B →* U.B ⊗[A] (U.B ⊗[A] U.B)) /
    (Units.map (p12 A U : U.B ⊗[A] U.B →* U.B ⊗[A] (U.B ⊗[A] U.B)) *
      Units.map (p23 A U : U.B ⊗[A] U.B →* U.B ⊗[A] (U.B ⊗[A] U.B)))

def cob0 (A : Type) [CommRing A] (U : Cov A) : U.Bˣ →* (U.B ⊗[A] U.B)ˣ :=
  Units.map (d0 A U : U.B →* U.B ⊗[A] U.B) / Units.map (d1 A U : U.B →* U.B ⊗[A] U.B)

def Z1 (A : Type) [CommRing A] (U : Cov A) : Subgroup (U.B ⊗[A] U.B)ˣ := (cob1 A U).ker

def B1 (A : Type) [CommRing A] (U : Cov A) : Subgroup (U.B ⊗[A] U.B)ˣ := (cob0 A U).range

abbrev Cech (A : Type) [CommRing A] (U : Cov A) : Type := Additive (Z1 A U ⧸ (B1 A U).subgroupOf (Z1 A U))

def cls (A : Type) [CommRing A] (U : Cov A) (u : Z1 A U) : Cech A U := Additive.ofMul (QuotientGroup.mk u)

def tmap (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) : (U.B ⊗[A] U.B)ˣ →* (V.B ⊗[A] V.B)ˣ :=
  Units.map (Algebra.TensorProduct.map g g : U.B ⊗[A] U.B →* V.B ⊗[A] V.B)

def LeafZMap : Prop := ∀ (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) (u : (U.B ⊗[A] U.B)ˣ),
  u ∈ Z1 A U → tmap A U V g u ∈ Z1 A V

theorem mem_Z1_iff_cocycle (A : Type) [CommRing A] (U : Cov A) (u : (U.B ⊗[A] U.B)ˣ) :
    u ∈ Z1 A U ↔ p13 A U (u : U.B ⊗[A] U.B) = p12 A U u * p23 A U u := by
  rw [Z1, MonoidHom.mem_ker, cob1, MonoidHom.div_apply, div_eq_one, MonoidHom.mul_apply, Units.ext_iff]
  simp

abbrev g3 (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) :
    U.B ⊗[A] (U.B ⊗[A] U.B) →ₐ[A] V.B ⊗[A] (V.B ⊗[A] V.B) :=
  Algebra.TensorProduct.map g (Algebra.TensorProduct.map g g)

theorem p12_tensorProduct_map_eq_g3_p12 (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) (x : U.B ⊗[A] U.B) :
    p12 A V (Algebra.TensorProduct.map g g x) = g3 A U V g (p12 A U x) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [p12]

theorem p13_tensorProduct_map_eq_g3_p13 (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) (x : U.B ⊗[A] U.B) :
    p13 A V (Algebra.TensorProduct.map g g x) = g3 A U V g (p13 A U x) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [p13]

theorem p23_tensorProduct_map_eq_g3_p23 (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) (x : U.B ⊗[A] U.B) :
    p23 A V (Algebra.TensorProduct.map g g x) = g3 A U V g (p23 A U x) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [p23]

theorem zmap : LeafZMap := by
  intro A _ U V g u hu
  rw [mem_Z1_iff_cocycle] at hu ⊢
  have ht : ((tmap A U V g u : (V.B ⊗[A] V.B)ˣ) : V.B ⊗[A] V.B) = Algebra.TensorProduct.map g g (u : U.B ⊗[A] U.B) := rfl
  rw [ht, p12_tensorProduct_map_eq_g3_p12, p13_tensorProduct_map_eq_g3_p13, p23_tensorProduct_map_eq_g3_p23, hu, map_mul]

def LeafDescH : Prop := Hyps → ∀ (A : Type) [CommRing A], ∃ c : ∀ U : Cov A, Cech A U ≃+ kerH A U,
  ∀ (U V : Cov A) (g : U.B →ₐ[A] V.B) (u : Z1 A U) (v : Z1 A V), (v : (V.B ⊗[A] V.B)ˣ) = tmap A U V g u →
    (c V (cls A V v) : H ℤ (sp A) Gm 1) = c U (cls A U u)

def LeafDescP : Prop := ∀ (A : Type) [CommRing A], ∃ c : ∀ U : Cov A, Cech A U ≃+ kerP A U,
  ∀ (U V : Cov A) (g : U.B →ₐ[A] V.B) (u : Z1 A U) (v : Z1 A V), (v : (V.B ⊗[A] V.B)ˣ) = tmap A U V g u →
    (c V (cls A V v) : Additive (CommRing.Pic A)) = c U (cls A U u)

theorem goal_of (hH : LeafDescH) (hP : LeafDescP) : LateralTheory.E.H1MultiplicativeGroup.LeafDesc := by
  intro hy A _
  obtain ⟨cH, hcH⟩ := hH hy A
  obtain ⟨cP, hcP⟩ := hP A
  refine ⟨fun U => (cH U).symm.trans (cP U), ?_⟩
  intro U V g x hU hV
  obtain ⟨u, hu⟩ : ∃ u : Z1 A U, cls A U u = (cH U).symm ⟨x, hU⟩ := by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul ((cH U).symm ⟨x, hU⟩))
    exact ⟨u, by rw [cls, hu]; rfl⟩
  let v : Z1 A V := ⟨tmap A U V g u, zmap A U V g u u.2⟩
  have h1 := hcH U V g u v rfl
  have h2 := hcP U V g u v rfl
  have hv : (cH V).symm ⟨x, hV⟩ = cls A V v := by
    apply (cH V).injective
    rw [AddEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [h1, hu, AddEquiv.apply_symm_apply]
  simp only [AddEquiv.trans_apply]
  rw [← hu, hv, h2]

end LateralTheory.E.LeafDescCut
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafLocStalkPf

def RelZS (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {U E : Spc} (u : U ⟶ E) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R u F m)) ∧ Function.Injective (pull R u F n)

end LateralTheory.E.LeafLocStalkPf
end
end
