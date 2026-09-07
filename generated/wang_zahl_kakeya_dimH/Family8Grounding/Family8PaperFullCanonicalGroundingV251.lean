import Family8Grounding.Family8PaperFullCanonicalGroundingV250
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalProp66AConsumerV2
import Family8Grounding.Family8PlankRetainedOwnerCubeWeightDenseBallV1
import Family8Grounding.Family8NormalizedLongIntervalWitnessV1

/-!
# Family 8 full canonical grounding checkpoint V251

This checkpoint combines three independent, fully checked advances.

* The adaptive selected-parent count is now consumed globally: the active
  parent cardinality and the finite supremum over occupied labels supply the
  natural Eq. (46) count loss automatically.  The genuine outer estimate and
  the inner scalar estimate for the same exact assembly remain explicit.
* Retained owner shadings now admit a common cube-weight dense-ball level with
  exact fine/coarse spatial restriction, packing control, and a radius-rho
  local mass band.  The paper lower bound for the common weight and the
  canonical-slab reassembly remain explicit.
* The long-terminal selector now produces a faithful parent-normalized
  `NormalizedLongIntervalWitness`.  It does not identify the normalized
  `C_F` values with the older absolute `fiberDeltaMax` witness, so no hidden
  parent-fibre mass loss is introduced.

Earlier unsuccessful drafts are deliberately absent from this import graph.
The remaining work is the analytic/geometry bridge joining these checked
combinatorial objects to the positive pointwise self-improvement endpoint.
-/
