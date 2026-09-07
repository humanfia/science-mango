import Family8Grounding.Family8PaperFullCanonicalGroundingV9
import Family8Grounding.Family8PaperConflictOwnerParentFramePhysicalBridgeV5
import Family8Grounding.Family8PaperConflictOwnerParentFrameFiniteCodeV8
import Family8Grounding.Family8PaperConflictOwnerParentFrameCoarseCoverV6
import Family8Grounding.Family8PaperConflictOwnerGlobalCoarseCoverV3
import Family8Grounding.Family8PaperConflictOwnerGlobalStickyScaleCoverV4
import Family8Grounding.Family8TubeJohnAxisWitnessLeOneV6
import Family8Grounding.Family8TubeJohnUnitRescalingGeometryLeOneV7
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnLongAxisRelabelV4
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnLongPackingMeanV2
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnDensityBudgetSelectorV2
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
import Family8Grounding.Family8Def212CUniformDyadicBridgeV2

/-!
# Full canonical paper-strength Family 8 grounding bundle, V10

This successor freezes three formerly open construction layers.

* The owner/parent frame code now has a literal `5 * rho` tube carrier,
  an honest `O(rho^-1)` finite code count, a global tagged aggregation, and
  a genuine `StickyScaleCover` after unused codes are removed.
* Every positive tube radius at most one has explicit John-axis data and an
  affine unit rescaling whose displayed outer ellipsoid maps exactly to the
  unit ball.
* The fixed-John translation selector now relabels an actual long axis,
  compares the exact finite mean to the long-axis packing mean, derives the
  paper cap from the literal maximal concentration, and chooses
  `J = max 1 (floor densityRatio)` without a positive-mean or scalar-budget
  callback.  The zero-floor and empty-family cases use the proved one-copy
  mean bound.

The dyadic fibre-cardinality bridge to Definition 2.12 `C`-uniformity is also
included.  This bundle does not claim doubled-parent partitioning for the
owner cover, nor the rescaled-fibre Convex Wolff axioms; those remain visible
geometric construction seams.
-/
