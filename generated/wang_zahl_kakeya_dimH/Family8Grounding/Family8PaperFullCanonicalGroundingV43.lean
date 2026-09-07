import Family8Grounding.Family8PaperFullCanonicalGroundingV42
import Family8Grounding.Family8CanonicalExactWeightedDef212EpsilonDependentStepV1

/-!
# Full canonical paper-strength Family 8 grounding bundle, V43

This checkpoint closes every numerical quantifier in the exact-incidence
fixed-epsilon route.  Given a requested target epsilon, it obtains the old
Frostman parameters at epsilon/4, chooses one explicit positive common loss
`q`, constructs a common terminal scale, and proves all density, selected
base-volume, conflict-degree, and RHS budgets.  The resulting datumwise
improvement uses actual multiscale/Def. 2.12 inputs and a sharp source
Katz--Tao bound.

The decrement is necessarily epsilon-dependent on this route.  A companion
theorem proves that the direct `2 * nu` budget cannot hold for every positive
target epsilon with one fixed positive `nu`.  Hence V43 does not disguise the
remaining central geometric gain or the two explicit datum-level producers
as a `FrostmanProperty` theorem.
-/
