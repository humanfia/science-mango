import Family8Grounding.Family8PaperFullCanonicalGroundingV24
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossEnvelopeV3

/-!
# Full canonical paper-strength Family 8 grounding bundle, V25

This successor removes the ceiling from the fixed-John greedy loss.  The
literal finite loss is bounded by the logarithmic tail times the sum of the
actual fixed-John paper caps plus two, both over `Real` and `ENNReal`; an
envelope-level density estimate therefore supplies the exact density premise
of the common selected Frostman/CWA connector.  Bounding the cap sum by an
explicit scale power is the remaining density-absorption step.
-/
