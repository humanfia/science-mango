import Family8Grounding.Family8ActualFamilyVolumePackingV1
import Family8Grounding.Family8AllFrostmanBranchV1

open scoped ENNReal NNReal
open MeasureTheory

namespace Family8AllFrostmanBranchFromCardPackingV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8ActualFamilyVolumePackingV1
open Family8AllFrostmanBranchNumericsV1
open Family8AllFrostmanBranchV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# The all-Frostman branch from the paper's tube-packing bound

This composes the actual cardinality-to-volume bridge with the exact
all-Frostman multiplicity endpoint.  The only remaining geometric inputs are
now displayed in their paper form: `#T <= C delta^(-4)` and the Sticky
union-volume lower bound.
-/

/-- The complete algebraic all-Frostman branch starting from a literal
`C delta^(-4)` bound on the number of essentially distinct tubes. -/
theorem averageMultiplicity_le_frostmanRHS_of_allFrostman_card_packing
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) {C : ENNReal}
    {epsilon gamma : Real}
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hdeltaThreshold :
      delta <= allFrostmanConstantThreshold (8 * C) epsilon gamma)
    (hCtop : C ≠ ∞) (hepsilon : 0 < epsilon)
    (hgamma0 : 0 <= gamma) (hgamma4 : gamma <= 4)
    (hcard :
      (Fintype.card iota : ENNReal) <=
        C * (delta : ENNReal) ^ (-4 : Real))
    (hunion :
      (delta : ENNReal) ^ (gamma / 2) <=
        volume D.shading.shadedUnion) :
    D.shading.averageMultiplicity <=
      frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon
        (gamma / 2) := by
  have hvolume :
      D.actualFamilyVolume <=
        (8 * C) * (delta : ENNReal) ^ (-2 : Real) :=
    actualFamilyVolume_le_of_card_rpow_neg_four
      D hdelta hdeltaHalf hcard
  have hEightCtop : (8 * C : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCtop
  exact averageMultiplicity_le_frostmanRHS_of_allFrostman_branch
    D hdelta hdeltaThreshold hEightCtop hepsilon hgamma0 hgamma4
      hvolume hunion

#print axioms
  averageMultiplicity_le_frostmanRHS_of_allFrostman_card_packing

end

end Family8AllFrostmanBranchFromCardPackingV1
