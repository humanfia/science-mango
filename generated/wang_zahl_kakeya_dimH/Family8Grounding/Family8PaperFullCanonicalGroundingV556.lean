import Family8Grounding.Family8PaperFullCanonicalGroundingV555
import Family8Grounding.Family8SelectedOccurrenceWeightedWinnerSideBucketV1
import Family8Grounding.Family8SupportedSourceActiveFineAverageReindexV1
import Family8Grounding.Family8SelectedOccurrenceFrozenSameQEq46ScalarSeamV1
import Family8Grounding.Family8SelectedOccurrenceNormalizedOuterDatumV1
import Family8Grounding.Family8SelectedOccurrenceOptionFrozenLossPowerV1
import Family8Grounding.Family8PlankThickControlAffineImageTransportV1

/-!
# Full canonical grounding interface checkpoint V556

The selected-occurrence route now performs an actual shaded-mass-weighted
winner-side bucket before freezing the exact-outer witness.  The retained
whole occurrence set has one common outer side label, loses only the explicit
winner-side logarithmic factor, and does not select or reselect a coarse
occurrence.

On that set, the exact Option-indexed outer family has a common scalar
normalization with exact average, density, Frostman-constant, and cardinality
transport.  Supported active-fine reindexing preserves the actual average,
and the fixed producer-chosen occurrence has a weak Cordoba scalar seam which
selects only its eventual inner side label rather than requiring a bound for
all occupied labels.  The Option-block frozen losses, including the literal
factor four, have an explicit small-power envelope.  Thickened-plank control
can be transported through a scalar dilation once the sharp source control
and scale inequalities are supplied.

The remaining object-level seam is a polylogarithmic fine-label-first mass
payment for the same frozen occurrence; a fallback linear loss by the number
of occurrences is deliberately not included here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV556

#print axioms
  Family8SelectedOccurrenceWeightedWinnerSideBucketV1.exists_selectedOccurrence_weightedWinnerSideBucket
#print axioms
  Family8SupportedSourceActiveFineAverageReindexV1.sourceActiveFineShading_averageMultiplicity_eq_of_support
#print axioms
  Family8SelectedOccurrenceFrozenSameQEq46ScalarSeamV1.exists_selectedOccurrenceFrozenSameQ_expandedCordobaScalar
#print axioms
  Family8SelectedOccurrenceNormalizedOuterDatumV1.selectedOccurrenceNormalizedOuterDatum
#print axioms
  Family8SelectedOccurrenceNormalizedOuterDatumV1.selectedOccurrenceNormalizedOuterFamily_isFrostmanIn
#print axioms
  Family8SelectedOccurrenceOptionFrozenLossPowerV1.selectedOccurrenceJointFrozenExternalLoss_le_rpow
#print axioms
  Family8PlankThickControlAffineImageTransportV1.frostmanThickenedPlankControl_scalarDilation

end Family8PaperFullCanonicalGroundingV556
