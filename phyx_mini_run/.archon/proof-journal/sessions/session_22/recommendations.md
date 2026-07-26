# Recommendations

- `PhyXMiniProblems/problem_phyx_mini_0909.lean` — One active `sorry` remains in `exit_velocity_components`, whose unchanged-horizontal-velocity conjunct is false under its current hypotheses because they omit the zero-horizontal-field readout.
- `PhyXMiniProblems/problem_phyx_mini_0967.lean` — PhyXMiniProblems.ProblemPhyXMini0967.finiteApparatusTorqueMagnitudeErrorBound remains closed by sorryAx and is not derivable from its sole approximation-law hypothesis.
- `PhyXMiniProblems/problem_phyx_mini_0971.lean` — The target depends on horizontal_kick_speed_tends_to_capacitor_impulse, whose proof contains an active `sorry`. SatisfiesNegligibleDisplacementAsymptotics.forceErrorIntegrable assumes integrability only of |F-F0|; this does not imply a.e. strong measurability of the signed force F, so the Bochner-integral transfer and positive impulse limit are not derivable.
