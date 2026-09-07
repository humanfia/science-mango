import Family8Grounding.Family8ParameterLadderSelfImprovementOrchestrationV1

open scoped ENNReal NNReal

namespace Family8NonzeroMassParameterEndpointOrchestrationV3

open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8ParameterLadderSelfImprovementOrchestrationV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Nonzero-mass datum endpoint for Main Lemma 1

Actual geometric decompositions need a surviving positive shading mass.
That restriction is harmless at the property boundary: if the source
shading mass is zero, its average multiplicity is identically zero.  Also,
the normalized requirement `delta0 <= 1/2` can be imposed mechanically by
capping any positive raw terminal scale.

This file removes both obligations from the remaining Section 8 producer.
No theorem input is stored in a structure, and the desired multiplicity
bound never appears as a premise.

V1 and V2 are failed notation/zero-division drafts and are not imported.
-/

/-- Cap an arbitrary raw validity scale by the normalization scale `1/2`. -/
def halfCappedScale (rawDelta0 : NNReal) : NNReal :=
  min rawDelta0 (2 : NNReal)⁻¹

theorem halfCappedScale_pos {rawDelta0 : NNReal}
    (hraw : 0 < rawDelta0) :
    0 < halfCappedScale rawDelta0 := by
  rw [halfCappedScale, lt_min_iff]
  exact ⟨hraw, by positivity⟩

theorem halfCappedScale_le_raw (rawDelta0 : NNReal) :
    halfCappedScale rawDelta0 <= rawDelta0 := by
  exact min_le_left _ _

theorem halfCappedScale_le_half (rawDelta0 : NNReal) :
    halfCappedScale rawDelta0 <= (2 : NNReal)⁻¹ := by
  exact min_le_right _ _

/-- It is enough to prove a fixed-parameter Frostman estimate on data with
nonzero source shading mass.  The zero-mass branch is definitionally zero. -/
theorem frostmanAtParameters_of_nonzero_shadingMass
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hbound : forall (delta : NNReal) (index : Type)
      [Fintype index] [DecidableEq index]
      (D : ActualTubeDatum delta index),
        D.IsAdmissible ->
        delta <= delta0 ->
        FrostmanHypotheses D eta ->
        D.shading.shadingMass ≠ 0 ->
        D.shading.averageMultiplicity <=
          frostmanMultiplicityRHS
            delta D.actualFamilyVolume epsilon beta) :
    FrostmanAtParameters beta epsilon eta delta0 := by
  intro delta index _ _ D hD hdelta hF
  by_cases hmass : D.shading.shadingMass = 0
  · unfold Shading.averageMultiplicity
    rw [hmass, ENNReal.zero_div]
    exact bot_le
  · exact hbound delta index D hD hdelta hF hmass

/-- Most concrete producer handoff currently needed by Main Lemma 1.

For a single ladder fixed outside `targetEpsilon`, the producer supplies a
positive loss exponent, a positive raw terminal scale, and the actual
multiplicity estimate only for nonzero-mass data.  Capping the scale,
handling zero mass, packaging `FrostmanAtParameters`, extracting the fixed
positive decrement, and all later bootstrap/boundary steps are automatic. -/
theorem mainLemmaOne_of_parameterLadderNonzeroMassEndpoint
    (hgeometry : forall beta gamma : Real,
      0 < beta -> beta < gamma -> gamma <= 1 ->
      KatzTaoProperty beta -> FrostmanProperty gamma ->
        exists epsilon0 : Real, exists P : ParameterLadder epsilon0 beta gamma,
          forall targetEpsilon : Real, 0 < targetEpsilon ->
            exists eta : Real, exists rawDelta0 : NNReal,
              0 < eta /\ 0 < rawDelta0 /\
                forall (delta : NNReal) (index : Type)
                  [Fintype index] [DecidableEq index]
                  (D : ActualTubeDatum delta index),
                    D.IsAdmissible ->
                    delta <= rawDelta0 ->
                    FrostmanHypotheses D eta ->
                    D.shading.shadingMass ≠ 0 ->
                    D.shading.averageMultiplicity <=
                      frostmanMultiplicityRHS
                        delta D.actualFamilyVolume targetEpsilon
                          (gamma - sectionEightFixedNu P))
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply mainLemmaOne_of_parameterLadderEndpoint
  intro target source htargetPos htargetSource hsourceOne hKT hFSource
  obtain ⟨epsilon0, P, hsource⟩ :=
    hgeometry target source htargetPos htargetSource hsourceOne hKT hFSource
  refine ⟨epsilon0, P, ?_⟩
  intro targetEpsilon htargetEpsilon
  obtain ⟨eta, rawDelta0, heta, hrawDelta0, hbound⟩ :=
    hsource targetEpsilon htargetEpsilon
  refine ⟨eta, halfCappedScale rawDelta0, heta,
    halfCappedScale_pos hrawDelta0,
    halfCappedScale_le_half rawDelta0, ?_⟩
  apply frostmanAtParameters_of_nonzero_shadingMass
  intro delta index _ _ D hD hdelta hF hmass
  exact hbound delta index D hD
    (hdelta.trans (halfCappedScale_le_raw rawDelta0)) hF hmass

#print axioms halfCappedScale_pos
#print axioms halfCappedScale_le_raw
#print axioms halfCappedScale_le_half
#print axioms frostmanAtParameters_of_nonzero_shadingMass
#print axioms mainLemmaOne_of_parameterLadderNonzeroMassEndpoint

end

end Family8NonzeroMassParameterEndpointOrchestrationV3
