import Family8Grounding.Family8PaperFullCanonicalGroundingV215
import Family8Grounding.Family8SelectedOccurrenceOwnerHullRefinementV2
import Family8Grounding.Family8SelectedOccurrenceOwnerHullUniqueOwnerV2
import Family8Grounding.Family8PlankThickControlLongTubeClusterDatumV2

/-!
# Family 8 full canonical grounding checkpoint V216

The selected-occurrence owner construction now uses the literal
representative-owner subfibre and its closed convex hull.  Parent purity,
containment in the actual parent tube, admissible thickening containment, and
unique ownership all follow from definitions, scale inequalities, and the
proved conflict-free owner selection; the two old callback seams disappear.

For the M-aware route, every literal thickened-plank cluster is now packaged
as a genuine same-index `ActualTubeDatum b`.  Nonemptiness, the `M` cardinality
bound, shading mass, shaded union, average multiplicity, body containment, and
the `M * b^2` family-volume bound are exact.  What remains is admissibility
(freshness and common unit-ball support) and Frostman transfer after tube-body
enlargement, together with quantified owner-subfibre mass selection and the
other scalar/global seams.
-/
