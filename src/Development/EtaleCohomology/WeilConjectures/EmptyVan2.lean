import Development.EtaleCohomology.WeilConjectures.GysinSeqCut

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et

namespace LateralTheory.EWeil.Gys.PurityCut
open LateralTheory.EWeil.Gys

abbrev pullE {l r : ℕ} {P' P : SPair l r} (f : P'.Hom P) (q : ℕ) (i n : ℤ) :
    HZ q i (initial.to P.Z) n →+ HZ q i (initial.to P'.Z) n :=
  pullZ q i (j := initial.to P.Z) (j' := initial.to P'.Z) f.fZ (𝟙 _) (initial.hom_ext _ _) n

def EmptyVan : Prop := ∀ (q : ℕ) (n i : ℤ), Subsingleton (Ht q (sch.obj (⊥_ Scheme.{0})) n i)

def Compare : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ),
  ∃ θ : ∀ (P : SPair l r) (c : ℕ) (i a b : ℤ), a + 2 * r = b →
      (HZ (l ^ c) i (initial.to P.Z) a ≃+ HZ (l ^ c) (i + r) P.j b),
    (∀ (P' P : SPair l r) (f : P'.Hom P) (c : ℕ) (i a b : ℤ) h x,
      θ P' c i a b h (pullE f (l ^ c) i a x) =
        pullZ _ _ f.fX f.fU f.sqU _ (θ P c i a b h x)) ∧
    ∀ (P : SPair l r) (c : ℕ) (i a b : ℤ) h x,
      θ P c i a b h (redZ (l ^ (c + 1)) (l ^ c) i (initial.to P.Z) a x) = redZ _ _ _ P.j _ (θ P (c + 1) i a b h x)

theorem goal_of (hS : SuppSeq) (hE : EmptyVan) (hC : Compare) : Purity := by
  intro hB l _ r
  obtain ⟨o, bd, hex, hnat, hred⟩ := hS
  obtain ⟨θ, hθn, hθr⟩ := hC hB l r
  have bij : ∀ (q : ℕ) (i : ℤ) (Z : Scheme.{0}) (n : ℤ), Function.Bijective (o q i (initial.to Z) n) := by
    intro q i Z n
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
      obtain ⟨z, rfl⟩ := ((hex q i (initial.to Z) m).2.2 x).1 hx
      have := hE q m i
      rw [Subsingleton.elim z 0, map_zero]
    · haveI := hE q n i
      exact ((hex q i (initial.to Z) n).1 y).1 (Subsingleton.elim _ _)
  let e : ∀ (q : ℕ) (i : ℤ) (Z : Scheme.{0}) (n : ℤ), HZ q i (initial.to Z) n ≃+ Ht q (sch.obj Z) n i :=
    fun q i Z n => AddEquiv.ofBijective (o q i (initial.to Z) n) (bij q i Z n)
  have he : ∀ q i Z n x, e q i Z n x = o q i (initial.to Z) n x := fun _ _ _ _ _ => rfl
  refine ⟨fun P c i a b h => (e (l ^ c) i P.Z a).symm.trans (θ P c i a b h), ?_, ?_⟩
  · intro P' P f c i a b h x
    simp only [AddEquiv.trans_apply]
    rw [← hθn]
    congr 1
    apply (e (l ^ c) i P'.Z a).injective
    rw [AddEquiv.apply_symm_apply, he, (hnat (l ^ c) i (initial.to P.Z) (initial.to P'.Z) f.fZ (𝟙 _)
      (initial.hom_ext _ _) a).1, ← he, AddEquiv.apply_symm_apply]
  · intro P c i a b h x
    simp only [AddEquiv.trans_apply]
    rw [← hθr]
    congr 1
    apply (e (l ^ c) i P.Z a).injective
    rw [AddEquiv.apply_symm_apply, he, (hred (l ^ (c + 1)) (l ^ c) i (initial.to P.Z) a).1, ← he,
      AddEquiv.apply_symm_apply]

end LateralTheory.EWeil.Gys.PurityCut
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.EWeil.EmptyVan₂

instance isEmpty_bot : IsEmpty (⊥_ Scheme.{0}) := by
  infer_instance

theorem sec_subsingleton {R : Type} [CommRing R] (G : Shv R) {U : Scheme.{0}} (f : U ⟶ ⊥_ Scheme.{0}) :
    Subsingleton (G.obj.obj (op U)) := by
  have : IsEmpty U := ⟨fun x => isEmptyElim (f.base x)⟩
  exact (ModuleCat.isZero_iff_subsingleton).1
    (IsTerminal.isZero (Sheaf.isTerminalOfBotCover G U (Scheme.bot_mem_grothendieckTopology U)))

theorem free_hom_subsingleton {R : Type} [CommRing R] (G : Shv R) :
    Subsingleton ((free R).obj (yoneda.obj (⊥_ Scheme.{0})) ⟶ G) := by
  constructor
  intro f g
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv _ _).injective
  ext U x
  by_cases h : Nonempty (U.unop ⟶ ⊥_ Scheme.{0})
  · obtain ⟨φ⟩ := h
    exact @Subsingleton.elim _ (sec_subsingleton G φ) _ _
  · have : IsEmpty (U.unop ⟶ ⊥_ Scheme.{0}) := not_nonempty_iff.1 h
    have hx : x = 0 := Finsupp.ext fun a => isEmptyElim (a.down : U.unop ⟶ ⊥_ Scheme.{0})
    subst hx
    simp only [map_zero]

theorem isZero_free {R : Type} [CommRing R] : IsZero ((free R).obj (yoneda.obj (⊥_ Scheme.{0}))) := by
  rw [IsZero.iff_id_eq_zero]
  have := free_hom_subsingleton (R := R) ((free R).obj (yoneda.obj (⊥_ Scheme.{0})))
  exact Subsingleton.elim _ _

end LateralTheory.EWeil.EmptyVan₂
end
end
