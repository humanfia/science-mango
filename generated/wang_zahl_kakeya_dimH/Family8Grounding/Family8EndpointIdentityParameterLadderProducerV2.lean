import Family8Grounding.Family8ParameterLadderV1

/-!
# Canonical parameter ladder for the endpoint-identity proof

ADD-only successor of V1.  The existential ladder binder is intentionally
anonymous so the strict unused-variable linter records no false positive.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8EndpointIdentityParameterLadderProducerV2

open Family8ParameterLadderV1

noncomputable section

/-- A fixed positive fraction of the improvement gap. -/
def endpointIdentityEpsilon0 (beta gamma : Real) : Real :=
  (gamma - beta) / 32

theorem endpointIdentityEpsilon0_pos
    {beta gamma : Real} (hgap : beta < gamma) :
    0 < endpointIdentityEpsilon0 beta gamma := by
  unfold endpointIdentityEpsilon0
  positivity

/-- The canonical ladder used by the endpoint-identity branch. -/
noncomputable def endpointIdentityParameterLadder
    {beta gamma : Real} (hbeta : 0 < beta) (hgap : beta < gamma) :
    ParameterLadder (endpointIdentityEpsilon0 beta gamma) beta gamma :=
  Classical.choice
    (exists_parameterLadder (endpointIdentityEpsilon0_pos hgap) hbeta hgap)

/-- Existential form consumed directly by the top-level orchestration. -/
theorem exists_endpointIdentityParameterLadder
    {beta gamma : Real} (hbeta : 0 < beta) (hgap : beta < gamma) :
    ∃ epsilon0 : Real, ∃ _P : ParameterLadder epsilon0 beta gamma,
      epsilon0 = endpointIdentityEpsilon0 beta gamma := by
  exact ⟨endpointIdentityEpsilon0 beta gamma,
    endpointIdentityParameterLadder hbeta hgap, rfl⟩

#print axioms endpointIdentityEpsilon0
#print axioms endpointIdentityEpsilon0_pos
#print axioms endpointIdentityParameterLadder
#print axioms exists_endpointIdentityParameterLadder

end

end Family8EndpointIdentityParameterLadderProducerV2
