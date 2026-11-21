import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx

private theorem UpperTheory.Reformulated.B.Gr34.fix_pi_iff {ι : Type} [Finite ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (∀ i, G i) M)
    (K : ∀ i, Subgroup (G i)) (m : M) :
    (∀ k ∈ Subgroup.pi Set.univ K, ρ k m = m) ↔ ∀ j, ∀ k ∈ K j, ρ (Pi.mulSingle j k) m = m := by
  refine ⟨fun h j k hk => h _ fun i _ => ?_, fun h k hk => ?_⟩
  · rcases eq_or_ne i j with rfl | hij
    · simpa using hk
    · simp [Pi.mulSingle_eq_of_ne hij]
  · let H : Subgroup (∀ i, G i) :=
      { carrier := {g | ρ g m = m}
        one_mem' := by simp
        mul_mem' := fun {a b} (ha : ρ a m = m) (hb : ρ b m = m) => show ρ (a * b) m = m by simp [ha, hb]
        inv_mem' := fun {a} (ha : ρ a m = m) => show ρ a⁻¹ m = m by
          conv_lhs => rw [← ha, Representation.inv_self_apply] }
    exact Subgroup.pi_mem_of_mulSingle_mem (H := H) k fun i => h i _ (hk i trivial)

section
open ValuativeRel IsLocalRing UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open UpperTheory.V.AlgebraTools
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Reformulated.B.Gr34.mem_UC
    {L : Type} [inst : Field L] [inst_1 : NumberField L] {n q : ℕ} {w : Fin q → Plc L}
    {A M : Type} [inst_2 : CommRing A] [inst_3 : AddCommGroup M] [inst_4 : Module A M]
    (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ)
    (m : M) :
    m ∈ fixd ρ (UC n w C) ↔ ∀ j, m ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) := by
  exact UpperTheory.Reformulated.B.Gr34.fix_pi_iff (G := fun j => GLw n (w j)) ρ _ m

end
