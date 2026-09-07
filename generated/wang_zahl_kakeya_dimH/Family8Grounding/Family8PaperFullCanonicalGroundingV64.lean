import Family8Grounding.Family8PaperFullCanonicalGroundingV63
import Family8Grounding.Family8NormalizedCFDividingWitnessFiniteSelectionV6

/-!
# Full canonical paper-strength Family 8 grounding bundle, V64

This checkpoint integrates the callback-free finite first-crossing theorem
with the canonical V63 chain.  For an admissible datum and its literal
coherent multiscale cover, the stopping trichotomy is now stated entirely in
terms of the actual `StickyScaleCover` produced by `intervalScaleCover`.
Thus a first normalized crossing is witnessed by a literal coherent interval
cover, and every preceding stage carries the corresponding literal lower
barrier.  The all-large and long-terminal alternatives are retained without
supplying a crossing value, cover, scale bound, or concentration comparison
as caller data.

This is the selection and identification of the first crossing only.  The
successor-scale factorization after that crossing and the remaining
paper-strength mass, density, and scale estimates of Lemma 5.11 are still
open.  Consequently the certified-plank Córdoba consumption, the one-step
self-improvement, and `mainLemmaOne` recorded as open in V63 are not closed by
this integration checkpoint.
-/
