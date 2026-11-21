import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftB

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

theorem pshShift : PshShiftStatement := plurisubharmonicShift_proof

end

end ReciprocityTheory.AnForm.M
