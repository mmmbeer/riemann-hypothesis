import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

noncomputable section

namespace GlobalTheory.GenTorsor

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X Y Z : Scheme.{0}}

def pb (a : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (h : W ≤ a ⁻¹ᵁ U) : Γ(X, U)ˣ →* Γ(Y, W)ˣ :=
  Units.map (a.appLE U W h).hom

lemma pb_pb (b : Z ⟶ Y) (a : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (h : V ≤ a ⁻¹ᵁ U) (h' : W ≤ b ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    pb b V W h' (pb a U V h x) = pb (b ≫ a) U W (h'.trans (b.preimage_mono h)) x := by
  ext
  change ((a.appLE U V h ≫ b.appLE V W h').hom) (x : Γ(X, U)) = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

lemma pb_congr {a b : Y ⟶ X} (e : a = b) {U : X.Opens} {W : Y.Opens} (h : W ≤ a ⁻¹ᵁ U)
    (h' : W ≤ b ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pb a U W h x = pb b U W h' x := by
  subst e; rfl

lemma pb_res (a : Y ⟶ X) {U V : X.Opens} {W : Y.Opens}
    (h : V ≤ U) (h' : W ≤ a ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    pb a V W h' (res h x) = pb a U W (h'.trans (a.preimage_mono h)) x :=
  (pb_pb a (𝟙 X) h h' x).trans (pb_congr (Category.comp_id a) _ _ _)

section Cover

variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

lemma le_iSup_range (hc : ∀ x : X, ∃ i y, a i y = x) (V : X.Opens) :
    V ≤ ⨆ i, V ⊓ (a i).opensRange := fun x hx => by
  obtain ⟨i, y, rfl⟩ := hc x
  exact Opens.mem_iSup.2 ⟨i, hx, y, rfl⟩




end Cover


theorem isRepresentable_of_cover (F : Scheme.{0}ᵒᵖ ⥤ Type)
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) (p : F ⟶ yoneda.obj X)
    {J : Type} (W : J → X.Opens) (hW : iSup W = ⊤) (T : J → Scheme.{0})
    (y : ∀ i, F.obj (op (T i))) (π : ∀ i, T i ⟶ W i)
    (hπ : ∀ i, p.app _ (y i) = π i ≫ (W i).ι)
    (h : ∀ i (Z : Scheme.{0}) (x : F.obj (op Z)) (b : Z ⟶ W i), p.app _ x = b ≫ (W i).ι →
      ∃! c : Z ⟶ T i, F.map c.op (y i) = x) : F.IsRepresentable := by
  let G : Sheaf Scheme.zariskiTopology.{0} Type := ⟨F, (isSheaf_iff_isSheaf_of_type _ _).2 hF⟩
  let f : ∀ i, yoneda.obj (T i) ⟶ G.1 := fun i => yonedaEquiv.symm (y i)
  have hp : ∀ i (Z : Scheme.{0}) (c : Z ⟶ T i), p.app _ (F.map c.op (y i)) = c ≫ π i ≫ (W i).ι := by
    intro i Z c
    rw [← hπ]
    exact ConcreteCategory.congr_hom (p.naturality c.op) (y i)
  have hf : ∀ i, IsOpenImmersion.presheaf (f i) := by
    intro i
    have : IsPullback (f i) (yoneda.map (π i)) p (yoneda.map (W i).ι) := by
      apply IsPullback.of_forall_isPullback_app
      rintro ⟨Z⟩
      rw [Types.isPullback_iff]
      refine ⟨?_, ?_, ?_⟩
      · ext c
        exact (hp i Z c).trans (Category.assoc _ _ _).symm
      · rintro c c' ⟨h1, -⟩
        exact (h i Z (F.map (Quiver.Hom.op c) (y i)) (c ≫ π i)
          ((hp i Z c).trans (Category.assoc _ _ _).symm)).unique rfl h1.symm
      · intro x b hb
        obtain ⟨c, hc, -⟩ := h i Z x b hb
        refine ⟨c, hc, ?_⟩
        change c ≫ π i = b
        rw [← cancel_mono (W i).ι, Category.assoc, ← hp, hc]
        exact hb
    exact (MorphismProperty.relative_isStableUnderBaseChange @IsOpenImmersion).of_isPullback this.flip
      (MorphismProperty.relative_map (inferInstanceAs (IsOpenImmersion (W i).ι)))
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
    constructor
    intro Z x
    let q : Z ⟶ X := p.app _ x
    let 𝒰 := Z.openCoverOfIsOpenCover (fun i => q ⁻¹ᵁ W i) (by
      rw [IsOpenCover, ← Scheme.Hom.preimage_iSup, hW]; rfl)
    refine GrothendieckTopology.superset_covering _ ?_ 𝒰.mem_grothendieckTopology
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    obtain ⟨c, hc, -⟩ := h i _ (F.map (q ⁻¹ᵁ W i).ι.op x) (q ∣_ W i) (by
      rw [morphismRestrict_ι]
      exact ConcreteCategory.congr_hom (p.naturality (q ⁻¹ᵁ W i).ι.op) x)
    refine ⟨(Sigma.ι (fun i => yoneda.obj (T i)) i).app _ c, ?_⟩
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (Sigma.ι_desc f i) _) c).trans hc
  exact Scheme.LocalRepresentability.isRepresentable hf

end GlobalTheory.GenTorsor
