import Family8Grounding.Family8PaperFullCanonicalGroundingV284
import Family8Grounding.Family8FullRefinementSourceTauCanonicalKatzTaoCoefficientV1

/-!
# Family 8 full canonical grounding checkpoint V285

The full-refinement source-to-tau path now supplies its own finite native
Katz--Tao constant from the actual every-scale hypothesis.  Reusing that
constant for the inner selected-parent estimate and applying the proved
card-weighted cancellation removes the raw parent and bucket cardinalities;
the entire adaptive Equation (46) coefficient is bounded by one explicit
negative power of `delta`.

The remaining Equation (46) seam is now purely numerical: compare this
displayed power with the Proposition 66 inner target using the canonical
ParameterLadder exponent relations.
-/
