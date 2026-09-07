import Family8Grounding.Family8PaperFullCanonicalGroundingV58
import Family8Grounding.Family8NormalizedCFDividingWitnessActualCoverBridgeV4

/-!
# Full canonical paper-strength Family 8 grounding bundle, V59

This checkpoint closes the missing geometric lower normalization between the
paper's parent-normalized fibre constant and the legacy absolute dividing
value.  Parent surjectivity supplies one actual fine child per active parent;
the proved tube-volume bounds then give

`delta^2 / (16 * rho^2) <= fibre mass / parent volume`

for positive radii at most one half.  Hence the computed normalized maximum,
times this explicit floor, is bounded by the actual `fiberDeltaMax`.  The
result is specialized without callbacks to the source-to-`tau`,
`tau`-to-`theta`, and buffered intermediate covers.

This also exposes a real mismatch in the older dividing-witness interface:
it requested the same normalized lower bound for the absolute value, omitting
the unavoidable `(delta / rho)^2 / 16` factor.  A faithful Lemma 7.7(A)
stopping producer must therefore work with the normalized quantity or carry
this scale factor explicitly.  That recursive producer, the paper-strength
Lemma 5.11/retubing chain, the analytic Proposition 6.6(A) estimates, the
instantiated self-improvement, and `mainLemmaOne` remain open here.
-/
