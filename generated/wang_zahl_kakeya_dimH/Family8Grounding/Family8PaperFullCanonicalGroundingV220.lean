import Family8Grounding.Family8PaperFullCanonicalGroundingV219
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullAggregateV2
import Family8Grounding.Family8PlankThickControlCenteredLongTubeClusterV4

/-!
# Family 8 full canonical grounding checkpoint V220

The max-owner refinement now aggregates its per-block quality estimate over
the actual selected occurrence set.  Refined mass is an exact finite sum,
the old selected outer mass and average multiplicity are bounded by the
explicit fibre-card loss times their parent-pure max-owner counterparts, and
the refined shaded union remains inside the old one.

The literal M-aware long-tube cluster datum is also translated by the actual
ambient center into a common radius-two ball, while preserving shading mass,
family volume, shaded-union volume, and average multiplicity exactly.  This
closes the common bounded-support part of admissibility; freshness and the
weighted Frostman/ambient-denominator transfer remain.
-/
