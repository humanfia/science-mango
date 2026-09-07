import Family8Grounding.Family8PointwiseSelfImprovementLimitOrchestrationV2

open scoped NNReal

namespace Family8ExplicitParameterSelfImprovementOrchestrationV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8PointwiseSelfImprovementLimitOrchestrationV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Exact parameter quantifiers for the remaining geometric theorem

This file unfolds the output `FrostmanProperty (gamma - nu)` in the sole
pointwise self-improvement premise left by the property-level orchestration.
The order of the quantifiers is essential:

* `nu` is selected after `beta`, `gamma`, `K_KT(beta)`, and `K_F(gamma)`,
  but before the requested Frostman loss `targetEpsilon`;
* `eta` and `delta0` may depend on `targetEpsilon`;
* the fixed-parameter conclusion is exactly the existing
  `FrostmanAtParameters`, hence quantifies over every admissible actual datum
  and contains no callback or desired conclusion as a premise.

Thus a bound which only gives
`forall targetEpsilon, exists nu, ...` is not the required geometric output:
it does not produce a single improved exponent.
-/

/-- Repackage the explicit fixed-parameter output into the already-proved
pointwise property orchestration.  This theorem displays, without an alias
or structure field, the unique remaining geometric theorem type. -/
theorem mainLemmaOne_of_positive_explicitParameterSelfImprovement
    (hgeometry : forall beta gamma : Real,
      0 < beta -> beta < gamma -> gamma <= 1 ->
      KatzTaoProperty beta -> FrostmanProperty gamma ->
        exists nu : Real, 0 < nu /\
          forall targetEpsilon : Real, 0 < targetEpsilon ->
            exists eta : Real, exists delta0 : NNReal,
              0 < eta /\ 0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
                FrostmanAtParameters (gamma - nu) targetEpsilon eta delta0)
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply mainLemmaOne_of_positive_pointwise_selfImprovement
  intro target source htargetPos htargetSource hsourceOne hKT hFSource
  obtain ⟨nu, hnu, hparameters⟩ :=
    hgeometry target source htargetPos htargetSource hsourceOne hKT hFSource
  refine ⟨nu, hnu, ?_⟩
  intro targetEpsilon htargetEpsilon
  exact hparameters targetEpsilon htargetEpsilon

/-- Unit-interval spelling of the same explicit parameter bridge. -/
theorem unitInterval_of_positive_explicitParameterSelfImprovement
    (hgeometry : forall beta gamma : Real,
      0 < beta -> beta < gamma -> gamma <= 1 ->
      KatzTaoProperty beta -> FrostmanProperty gamma ->
        exists nu : Real, 0 < nu /\
          forall targetEpsilon : Real, 0 < targetEpsilon ->
            exists eta : Real, exists delta0 : NNReal,
              0 < eta /\ 0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
                FrostmanAtParameters (gamma - nu) targetEpsilon eta delta0) :
    forall beta : Real, 0 <= beta -> beta <= 1 ->
      KatzTaoProperty beta -> FrostmanProperty beta := by
  apply unitInterval_of_positive_pointwise_selfImprovement
  intro target source htargetPos htargetSource hsourceOne hKT hFSource
  obtain ⟨nu, hnu, hparameters⟩ :=
    hgeometry target source htargetPos htargetSource hsourceOne hKT hFSource
  exact ⟨nu, hnu, hparameters⟩

#print axioms mainLemmaOne_of_positive_explicitParameterSelfImprovement
#print axioms unitInterval_of_positive_explicitParameterSelfImprovement

end

end Family8ExplicitParameterSelfImprovementOrchestrationV1
