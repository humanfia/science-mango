import Family8Grounding.Family8PaperFullCanonicalGroundingV217
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleFlatnessTransportV3

/-!
# Family 8 full canonical grounding checkpoint V218

The missing paper-flatness datum now has an exact transport into the actual
occupied dyadic bucket.  For a retained member in the common John frame, the
ceil-log discretization costs only a factor two and gives

`bucketShortA <= 2 * min(side 0, side 1) / sideShapeUpper label 2`.

Consequently the paper thin/flat branch only has to produce the corresponding
memberwise short-to-long inequality with a positive `delta`-power target; no
additional bucket argument or callback is needed downstream.
-/
