import ArchonPhysics.ActualSixSiteNearResonantModularPolynomialQuinticFormula

/-! Evaluation of the three defining quotient quintics. -/

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation

open ArchonPhysics.ActualSixSiteNearResonantModularPolynomialInverse
open ArchonPhysics.ActualSixSiteNearResonantModularCompanionQuintic

noncomputable section

theorem companionEvaluation_quotientQuintic103 (r : SpectralVariable) :
    companionEvaluation (quotientQuintic103 r) = 0 := by
  rw [companionEvaluation_quotientQuintic103_formula]
  fin_cases r
  · change matrixQuintic103 (tensorPower
      (Finsupp.single (0 : SpectralVariable) 1)) = 0
    rw [tensorPower_single_zero, matrixQuintic103_map,
      matrixQuintic103_companion103, map_zero]
  · change matrixQuintic103 (tensorPower
      (Finsupp.single (1 : SpectralVariable) 1)) = 0
    rw [tensorPower_single_one, matrixQuintic103_map,
      matrixQuintic103_companion103, map_zero]
  · change matrixQuintic103 (tensorPower
      (Finsupp.single (2 : SpectralVariable) 1)) = 0
    rw [tensorPower_single_two, matrixQuintic103_map,
      matrixQuintic103_companion103, map_zero]

end

end ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation
