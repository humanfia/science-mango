import Family8Grounding.Family8CommonPointTubePackingV1
import Family8Grounding.Family8AllFrostmanBranchFromPointwisePackingV1
import Mathlib.Tactic

open scoped ENNReal NNReal
open MeasureTheory

namespace Family8AllFrostmanBranchFromCommonPointPackingV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8PointwisePackingVolumeV1
open Family8CommonPointTubePackingV1
open Family8AllFrostmanBranchFromPointwisePackingV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# The all-Frostman branch with automatic common-point packing

The pointwise packing premise in the generic all-Frostman connector is not
an open geometric input: it follows from the proved common-point packing
theorem for admissible actual tube data at scales at most `1 / 100`.

This module folds that honest geometric restriction into the terminal scale
and removes the pointwise-packing theorem argument.  The only remaining
branch input is the literal Sticky union-volume lower bound.
-/

/-- Terminal scale simultaneously satisfying the all-Frostman numerical
threshold and the geometric small-radius regime of common-point packing. -/
def allFrostmanCommonPointPackingThreshold
    (epsilon gamma : Real) : NNReal :=
  min
    (allFrostmanPointwisePackingThreshold
      commonPointTubePackingConstant epsilon gamma)
    (1 / 100 : NNReal)

theorem allFrostmanCommonPointPackingThreshold_pos
    (epsilon gamma : Real) :
    0 < allFrostmanCommonPointPackingThreshold epsilon gamma := by
  rw [allFrostmanCommonPointPackingThreshold, lt_min_iff]
  exact ⟨allFrostmanPointwisePackingThreshold_pos
      commonPointTubePackingConstant epsilon gamma, by positivity⟩

theorem allFrostmanCommonPointPackingThreshold_le_half
    (epsilon gamma : Real) :
    allFrostmanCommonPointPackingThreshold epsilon gamma ≤
      (2 : NNReal)⁻¹ := by
  exact (min_le_left _ _).trans
    (allFrostmanPointwisePackingThreshold_le_half
      commonPointTubePackingConstant epsilon gamma)

/-- The actual common-point packing theorem automatically supplies both the
pointwise natural-number cap and its scale-invariant `delta^-2` bound. -/
theorem averageMultiplicity_le_frostmanRHS_of_allFrostman_commonPointPacking
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {epsilon gamma : Real}
    (hdeltaThreshold :
      delta ≤ allFrostmanCommonPointPackingThreshold epsilon gamma)
    (hepsilon : 0 < epsilon)
    (hgamma0 : 0 ≤ gamma) (hgamma4 : gamma ≤ 4)
    (hunion :
      (delta : ENNReal) ^ (gamma / 2) ≤
        volume D.shading.shadedUnion) :
    D.shading.averageMultiplicity ≤
      frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon
        (gamma / 2) := by
  have hdeltaNumeric :
      delta ≤ allFrostmanPointwisePackingThreshold
        commonPointTubePackingConstant epsilon gamma :=
    hdeltaThreshold.trans (min_le_left _ _)
  have hdeltaGeometric : delta ≤ (1 / 100 : NNReal) :=
    hdeltaThreshold.trans (min_le_right _ _)
  obtain ⟨M, hpoint, hcap⟩ :=
    exists_actualCarrierShading_commonPointTubePackingNatCap
      D hD hdeltaGeometric
  exact
    averageMultiplicity_le_frostmanRHS_of_allFrostman_pointwisePacking
      D hD M hdeltaNumeric commonPointTubePackingConstant_ne_top
        hepsilon hgamma0 hgamma4 hpoint hcap hunion

/-- Quantified all-Frostman endpoint with pointwise packing discharged.  The
remaining theorem argument is exactly the genuine union-volume producer; it
is neither stored in data nor replaced by a multiplicity conclusion. -/
theorem frostmanAtParameters_halfExponent_of_commonPointPacking
    {epsilon eta gamma : Real}
    (hepsilon : 0 < epsilon)
    (hgamma0 : 0 ≤ gamma) (hgamma4 : gamma ≤ 4)
    (hunion :
      ∀ {delta : NNReal} {iota : Type}
        [Fintype iota] [DecidableEq iota]
        (D : ActualTubeDatum delta iota),
        D.IsAdmissible → FrostmanHypotheses D eta →
          (delta : ENNReal) ^ (gamma / 2) ≤
            volume D.shading.shadedUnion) :
    FrostmanAtParameters (gamma / 2) epsilon eta
      (allFrostmanCommonPointPackingThreshold epsilon gamma) := by
  intro delta iota _ _ D hD hdelta hF
  exact
    averageMultiplicity_le_frostmanRHS_of_allFrostman_commonPointPacking
      D hD hdelta hepsilon hgamma0 hgamma4 (hunion D hD hF)

#print axioms allFrostmanCommonPointPackingThreshold_pos
#print axioms allFrostmanCommonPointPackingThreshold_le_half
#print axioms
  averageMultiplicity_le_frostmanRHS_of_allFrostman_commonPointPacking
#print axioms frostmanAtParameters_halfExponent_of_commonPointPacking

end
end Family8AllFrostmanBranchFromCommonPointPackingV1
