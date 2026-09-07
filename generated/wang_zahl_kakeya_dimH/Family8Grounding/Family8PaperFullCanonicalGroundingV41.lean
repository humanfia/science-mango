import Family8Grounding.Family8PaperFullCanonicalGroundingV40
import Family8Grounding.Family8StickySelectedParentGreedyBlockAutomaticFrostmanV4

/-!
# Full canonical paper-strength Family 8 grounding bundle, V41

This checkpoint makes the selected-parent greedy-block fallback completely
automatic.  Nonemptiness and the literal coarse-tube volume lower bound give
`rho^2 / 2` as a lower bound for the winning hull, hence the canonical
Frostman constant in the radius-four ambient is at most `1024 / rho^2`.

The fixed `rho^-2` loss is deliberately recorded as a fallback, not claimed
as the paper-small loss.  The main line still needs the flat-prism/local
multiscale improvement of this hull-volume bound, along with active-coarse
admissibility, the strongly-non-sticky endpoint, quantified scale-cover
assembly, second-long geometry, and the central unit-interval iteration.
-/
