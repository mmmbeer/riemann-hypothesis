import Formalism.WachLatticeTwists.SplitLocalLifts.StatCompColk
import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.DualWByLettersExtended
import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.SelmerInjColumnPlace
import Formalism.WachLatticeTwists.TorsionLengthCounts.RowCol
import Formalism.WachLatticeTwists.LatticeDualFibres.PropLocContOfLattices

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N2

theorem natCast_pow_smul (ℓ : ℕ) [Fact ℓ.Prime] {O : Type*} [CommRing O] [Algebra ℤ_[ℓ] O]
    {H : Type*} [AddCommGroup H] [Module O H] [Module ℤ_[ℓ] H] [IsScalarTower ℤ_[ℓ] O H]
    (e : ℕ) (x : H) : ((ℓ : ℤ_[ℓ]) ^ e) • x = ((ℓ : O) ^ e) • x := by
  rw [← algebraMap_smul O ((ℓ : ℤ_[ℓ]) ^ e) x, map_pow, map_natCast]

theorem scal : StatScal := by
  intro ℓ _ O _ _ H₁ H₂ _ _ _ _ _ _ _ _ Hf₁ Hf₂ g e
  constructor
  · intro h κ hκ
    obtain ⟨κ₁, h₁, h₂⟩ := h κ hκ
    exact ⟨κ₁, h₁, by rw [← natCast_pow_smul ℓ]; exact h₂⟩
  · intro h κ hκ
    obtain ⟨κ₁, h₁, h₂⟩ := h κ hκ
    exact ⟨κ₁, h₁, by rw [natCast_pow_smul ℓ (O := O)]; exact h₂⟩

theorem mono : StatMono := by
  intro O _ ℓ H₁ H₂ _ _ _ _ Hf₁ Hf₂ g e e' hee h κ hκ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hee
  rw [pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ (h κ hκ)

theorem prodB_lift (ℓ : ℕ) [Fact ℓ.Prime] {H₁ H₂ : Type} [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ) (h : ProdB ℓ Hf₁ Hf₂ g e) : LiftZ ℓ Hf₁ Hf₂ g e := by
  obtain ⟨A, _, _, B, M, u, s, H, jumps, D₀, D₁, D₂, _, _, _, _, _, _, _, _, _, _, _, _, W₀, W₁, W₂,
    S, cl₁, cl₂, I, _, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, a20, a21, rfl⟩ := h
  exact lifting_theorem.1 ℓ A B M u s H jumps a1 a2 a3 a4 a5 a6 a7 D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂
    g I a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21

theorem prodA_lift (ℓ : ℕ) [Fact ℓ.Prime] {H₁ H₂ : Type} [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ) (h : ProdA ℓ Hf₁ Hf₂ g e) : LiftZ ℓ Hf₁ Hf₂ g e := by
  obtain ⟨h2, A, _, _, B, M, u, H, jumps, c, D₀, D₁, D₂, _, _, _, _, _, _, _, _, _, _, _, _, W₀, W₁,
    W₂, S, δ, cl₁, cl₂, I, _, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
    a17, a18, a19, rfl⟩ := h
  exact lifting_theorem.2.1 ℓ h2 A B M u H jumps c a1 a2 a3 a4 a5 D₀ D₁ D₂ W₀ W₁ W₂ S δ H₁ H₂ cl₁ cl₂ Hf₁
    Hf₂ g I a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19

theorem src : StatSrc := by
  intro ℓ _ H₁ H₂ _ _ _ _ Hf₁ Hf₂ g e h
  rcases h with h | h | h
  · exact prodB_lift ℓ Hf₁ Hf₂ g e h
  · exact prodA_lift ℓ Hf₁ Hf₂ g e h
  · obtain ⟨K₁, K₂, _, _, _, _, Kf₁, Kf₂, hh, res₂, cor₁, cor₂, n, E, b1, b2, b3, b4, b5, b6, rfl⟩ := h
    refine lifting_theorem.2.2 ℓ K₁ K₂ H₁ H₂ Kf₁ Kf₂ Hf₁ Hf₂ hh g res₂ cor₁ cor₂ n E b1 b2 b3 b4 b5 ?_
    rcases b6 with b6 | b6
    · exact prodB_lift ℓ Kf₁ Kf₂ hh E b6
    · exact prodA_lift ℓ Kf₁ Kf₂ hh E b6

theorem srcO : StatSrcO := by
  intro ℓ _ O _ _ H₁ H₂ _ _ _ _ _ _ _ _ Hf₁ Hf₂ g e' h
  obtain ⟨e, he, h⟩ := h
  exact mono O ℓ H₁ H₂ Hf₁ Hf₂ g e e' he
    ((scal ℓ O H₁ H₂ Hf₁ Hf₂ g e).1 (src ℓ H₁ H₂ _ _ _ e h))

end Formalism.RepresentationBoundsCohomology.JL
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem liftCoc : StatLiftCoc := by
  intro O D M₁ M₂ _ _ _ _ _ _ ρ₁ ρ₂ p hp hs Hf₁ Hf₂ ℓ e hL κ hκ
  obtain ⟨x, hx, hxe⟩ := hL _ hκ
  obtain ⟨K₀, rfl⟩ := Submodule.mkQ_surjective _ x
  have h1 : (Submodule.Quotient.mk (cocycles1MapOfEquivariant ρ₁ ρ₂ p hp K₀ - ((ℓ : O) ^ e) • κ) : H1z ρ₂) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero]
    exact hxe
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
  obtain ⟨v, hv⟩ := h1
  obtain ⟨w, rfl⟩ := hs v
  let cb : coZ1s ρ₁ := ⟨fun g => ρ₁ g w - w, fun g h => by
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel⟩
  refine ⟨K₀ - cb, ?_, fun g => ?_⟩
  · have hcb : Submodule.mkQ _ cb = (0 : H1z ρ₁) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact ⟨w, by funext g; rfl⟩
    rw [map_sub, hcb, sub_zero]
    exact hx
  · have h2 : ρ₂ g (p w) - p w = p ((K₀ : D → M₁) g) - ((ℓ : O) ^ e) • (κ : D → M₂) g :=
      congrFun hv g
    show p ((K₀ : D → M₁) g - (ρ₁ g w - w)) = _
    rw [map_sub, map_sub, hp, h2]
    abel

theorem colK : StatColK := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ L _ _ _ _ r χ Dl inc v₁ ev hev hs Hf₁ Hf₂ ℓ e' j κ κz hκ hκf hL
  have key := fun a => liftCoc O Dl P L _ _ ev (ev_equiv r χ Dl inc v₁ ev hev) hs Hf₁ Hf₂ ℓ e' hL
    (κz a) (hκf a)
  choose Kz hKz1 hKz2 using key
  refine ⟨fun a g => if h : g ∈ Dl then inc ((Kz a : Dl → P) ⟨g, h⟩) else 0, Kz, ?_, hKz1, ?_⟩
  · intro a g
    dsimp only
    rw [dif_pos g.2]
  · intro a g hg
    dsimp only
    rw [dif_pos hg, ← hev, hKz2 a ⟨g, hg⟩, hκ a ⟨g, hg⟩]

theorem colk : StatColk := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ M _ _ _ r χ E δO Dl inc ev hE hM hev hs Hf₁ Hf₂ ℓ e' u uz huz hmem hL
  obtain ⟨kz, hk1, hk2⟩ := liftCoc O Dl P _ _ _ ev (ev_equiv_triv r χ Dl ev hev) hs Hf₁ Hf₂ ℓ e' hL
    uz hmem
  refine ⟨fun g => if h : g ∈ Dl then inc ((kz : Dl → P) ⟨g, h⟩) else 0, kz, ?_, hk1, ?_, ?_⟩
  · intro g
    dsimp only
    rw [dif_pos g.2]
  · intro g
    dsimp only
    split_ifs with h
    · exact hE _
    · exact ⟨0, (zero_mul E).symm⟩
  · intro g hg m
    dsimp only
    rw [dif_pos hg, hM, hk2 ⟨g, hg⟩, Submodule.coe_smul, huz ⟨g, hg⟩, smul_eq_mul, mul_assoc]

theorem colFun : StatColFun := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ V _ _ r χ Dl inc Hf₁ Lf H K Kz hK hKz s
  have h := H ((LinearMap.toSpanSingleton A V s).comp inc) Kz hKz
  have e : (fun g : Dl => K g • s) =
      fun g : Dl => ((LinearMap.toSpanSingleton A V s).comp inc) ((Kz : Dl → P) g) := by
    funext g
    rw [hK g]
    rfl
  rw [e]
  exact h

end Formalism.RepresentationBoundsCohomology.JL
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem compColK : StatCompColK := by
  intro ℓ _ O _ _ A T' G _ _ _ _ P _ _ _ _ _ _ L _ _ _ _ _ _ r χ Dl inc v₁ ev hev hsurj Hf₁ Hf₂ e' j κ κz
    hκz hκ hS
  obtain ⟨Kc, Kz, h1, h2, h3⟩ := colK O A T' G P L r χ Dl inc v₁ ev hev hsurj Hf₁ Hf₂ ℓ e' j κ κz hκz hκ
    (srcO ℓ O _ _ Hf₁ Hf₂ _ e' hS)
  exact ⟨Kc, ⟨Kz, h1, h2⟩, h3⟩

theorem compColk : StatCompColk := by
  intro ℓ _ O _ _ A T' G _ _ _ _ P _ _ _ _ _ _ M _ _ _ r χ E δO Dl inc ev hE hM hev hsurj Hf₁ Hf₂ e' u uz
    huz hu hS
  obtain ⟨k0, kz, h1, h2, h3, h4⟩ := colk O A T' G P M r χ E δO Dl inc ev hE hM hev hsurj Hf₁ Hf₂ ℓ e'
    u uz huz hu (srcO ℓ O _ _ Hf₁ Hf₂ _ e' hS)
  exact ⟨k0, ⟨kz, h1, h2⟩, h3, h4⟩

end Formalism.RepresentationBoundsCohomology.JL
end
end
