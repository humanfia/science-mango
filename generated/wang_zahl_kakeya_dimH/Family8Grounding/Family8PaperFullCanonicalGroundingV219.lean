import Family8Grounding.Family8PaperFullCanonicalGroundingV218
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullQualityV3

/-!
# Family 8 full canonical grounding checkpoint V219

The parent-specific occurrence refinement now chooses a genuine quality
owner rather than an arbitrary first witness.  In each global greedy block it
selects a fine carrier of maximal shaded measure, uses its actual Sticky
parent, and forms the corresponding parent-specific subfibre hull and shading.
Finite union subadditivity gives the explicit per-block comparison

`old outer carrier mass <= block fibre card * refined owner carrier mass`.

Thus the remaining owner-selection work is quantitative aggregation of this
literal fibre-card loss, followed by the conflict-free weighted selection and
the already proved refined unique-owner/local-Delta machinery.
-/
