import Family8Grounding.Family8PaperFullCanonicalGroundingV67
import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV10

/-!
# Full canonical paper-strength Family 8 grounding bundle, V68

This checkpoint adds the explicit absorption of the selected-parent cubic
dyadic-label loss.  V10 works with the literal
`Int.ceil`/`Int.toNat` bucket count from V9, bounds its cube by a finite
coefficient times a small negative power, and then uses an explicit positive
small-delta threshold to absorb that coefficient.  Hence the actual
`O(log(1/rho)^3)` selected-parent loss, multiplied by any fixed finite
constant, is now bounded by `rho ^ (-lossEta)` for every prescribed positive
`lossEta`; this is not assumed through a replacement power-law premise.

Together with V67, the genuine `a x b x 1` plank overlap and Cordoba
summation retain the actual `a / b` gain.  The remaining analytic-geometric
interface is still the paper-strength finite angle assignment and its
inverse-sine/container containment/container-scale estimates for the actual
selected bucket.  The two-scale Section 8 composition and `mainLemmaOne`
remain open downstream of those producers.
-/
