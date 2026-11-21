import Development.EtaleCohomology.WeilConjectures.GysinSeqCut

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.Gys.LV
open LateralTheory.EWeil LateralTheory.EWeil.Gys

def LowVan : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ), n < 2 * r →
  ∀ x : HZ (l ^ c) i P.j n, x = 0

def PointVan : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ), 2 * r < n →
  ∀ (x : HZ (l ^ c) i P.j n) (t : P.X), ∃ (P' : SPair l r) (f : P'.Hom P),
    t ∈ Set.range f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0

def Glue : Prop := ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ) (x : HZ (l ^ c) i P.j n),
  (∀ t : P.X, ∃ (P' : SPair l r) (f : P'.Hom P), t ∈ Set.range f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0) →
  ∃ (P' : SPair l r) (f : P'.Hom P), Surjective f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0

def SPair.idHom {l r : ℕ} (P : SPair l r) : P.Hom P where
  fX := 𝟙 _
  fZ := 𝟙 _
  fU := 𝟙 _
  etale := inferInstance
  sqZ := IsPullback.of_horiz_isIso ⟨by simp⟩
  sqU := by simp

theorem goal_of (hL : LowVan) (hP : PointVan) (hG : Glue) : Gys.LocalVan := by
  intro hB l _ r P c i n hn x
  rcases lt_or_gt_of_ne hn with h | h
  · refine ⟨P, SPair.idHom P, show Surjective (𝟙 P.X) from inferInstance, ?_⟩
    rw [hL hB l r P c i n h x, map_zero]
  · exact hG l r P c i n x (fun t => hP hB l r P c i n h x t)

end LateralTheory.EWeil.Gys.LV
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.Gys.LV.GluePf
open LateralTheory.EWeil LateralTheory.EWeil.Gys LateralTheory.EWeil.Gys.LV

def ShvSigma : Prop := ∀ (R : Type) [CommRing R] (F : GlobalTheory.EtC.Shv R) {T : Type} {Y : T → Scheme.{0}} (c : Cofan Y), IsColimit c →
  Function.Bijective (fun (s : GlobalTheory.EtC.Sec F c.pt) (t : T) => GlobalTheory.EtC.Sec.res (c.inj t) s)

end LateralTheory.EWeil.Gys.LV.GluePf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EWeil.Gys.LV.GluePf

theorem shvSigma : ShvSigma := by
  intro R _ F T Y c hc
  let G : Scheme.{0}ᵒᵖ ⥤ Type 1 := F.obj ⋙ forget _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology G :=
    Presieve.isSheaf_of_le G Scheme.zariskiTopology_le_etaleTopology
      ((isSheaf_iff_isSheaf_of_type _ G).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget _)).1 F.property))
  have : PreservesLimitsOfShape (Discrete T) G := preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hG
  let hL : IsLimit (G.mapCone c.op) := isLimitOfPreserves G (Cofan.IsColimit.op hc)
  let e := Types.isLimitEquivSections hL
  have he : ∀ s t, (e s).1 ⟨t⟩ = GlobalTheory.EtC.Sec.res (c.inj t) s := fun s t => rfl
  constructor
  · intro s₁ s₂ h
    apply e.injective
    apply Subtype.ext
    funext ⟨t⟩
    rw [he, he]
    exact congrFun h t
  · intro y
    let sec : (Discrete.functor (fun a => op (Y a)) ⋙ G).sections :=
      ⟨fun j => y j.as, by
        rintro ⟨j⟩ ⟨j'⟩ ⟨⟨h⟩⟩
        cases h
        show G.map (𝟙 _) _ = _
        rw [G.map_id]; rfl⟩
    refine ⟨e.symm sec, ?_⟩
    funext t
    show GlobalTheory.EtC.Sec.res (c.inj t) (e.symm sec) = y t
    rw [← he, e.apply_symm_apply]

end LateralTheory.EWeil.Gys.LV.GluePf
end
end
