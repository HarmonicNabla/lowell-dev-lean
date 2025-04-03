import Mathlib.Tactic -- imports some portion of Mathlib
import Mathlib.Util.Delaborators
import Mathlib.Analysis.SpecialFunctions.Integrals

set_option linter.unusedTactic false

namespace Course

noncomputable abbrev length := @MeasureTheory.volume ℝ inferInstance

end Course
