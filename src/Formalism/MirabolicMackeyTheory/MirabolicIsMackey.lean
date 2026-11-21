import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ErrSum
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxFull
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxPsiGood
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LemmaGG
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Mirabolic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.UnipotentNumeric
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OnExport
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OnLocal
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.AbsorbLocalConditions
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ThreeForms

namespace Formalism.EigenvalueLevelCeiling

theorem idxMono : IdxMono := index_monotone
theorem idxScaleIn : IdxScaleIn := index_scale_inclusion
theorem idxCutLe : IdxCutLe := index_truncation_le
theorem idxTransport : IdxTransport := index_transport
theorem latInter : LatInter := lattice_intersection
theorem threeForms : ThreeForms := three_forms
theorem idxFull : IdxFull := by
  unfold IdxFull
  intro K _ _ _ Z _ _ _ _ _ w M Th ThK hM hTh hThK _ σ hσ hsc E r h
  obtain ⟨hL, heq⟩ := idxScaleIn K Z w ⊤ M ThK hM hThK σ hσ
  have hmono := idxMono K Z w ⊤ M Th (sc σ ThK) hM hTh hL hsc
  rw [heq, finrank_top] at hmono
  have h2 : (lix w M ThK : ℝ) + (Module.finrank K Z : ℝ) * (Formalism.DivisionValues.vw w σ : ℝ) ≤ (lix w M Th : ℝ) := by
    exact_mod_cast hmono
  nlinarith
theorem idxPsiGood : IdxPsiGood := idxPsiGood_of idxMono idxScaleIn idxCutLe latInter
theorem lemmaGG : LemmaGG := good_index_GG
theorem mirabolicIsMackey : MirabolicIsMackey := mirabolic_is_mackey
theorem onLocal : OnLocal := onLocal_of idxMono idxCutLe idxTransport latInter threeForms idxPsiGood lemmaGG
theorem ramBasic : RamBasic := ramified_basic_bound

end Formalism.EigenvalueLevelCeiling
