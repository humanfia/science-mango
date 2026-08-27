import ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation

/-! The defining quintic evaluated by the tensor companion ring homomorphism. -/

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation

open ArchonPhysics.ActualSixSiteNearResonantModularPolynomialInverse
open ArchonPhysics.ActualSixSiteNearResonantModularCompanionQuintic

noncomputable section

theorem companionEvaluation_quotientQuintic103_formula (r : SpectralVariable) :
    companionEvaluation (quotientQuintic103 r) =
      matrixQuintic103 (tensorPower (Finsupp.single r 1)) := by
  unfold quotientQuintic103 matrixQuintic103
  simp only [map_add, map_mul, map_pow, companionEvaluation_C,
    companionEvaluation_X, Matrix.smul_mul, one_mul]

end

end ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation
