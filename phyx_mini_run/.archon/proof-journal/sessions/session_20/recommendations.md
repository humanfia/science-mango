# Recommendations

- `PhyXMiniProblems/problem_phyx_mini_0825.lean` — Direct Lean compilation fails inside axialMomentOfInertia_eq_twoFifths_mass_mul_radius_sq, so the target theorem is not kernel-checked; transitive axiom verification also never completed.
- `PhyXMiniProblems/problem_phyx_mini_0869.lean` — The frozen target is false under the encoded primary graph and potential-difference law, and its proof still depends on three active sorry gaps.
- `PhyXMiniProblems/problem_phyx_mini_0897.lean` — The theorem proof does not compile, so no accepted Lean proof exists despite the absence of escape hatches.
- `PhyXMiniProblems/problem_phyx_mini_0898.lean` — Direct Lean compilation fails on the AnswerChoice.C branch of the final unique-nearest proof.
- `PhyXMiniProblems/problem_phyx_mini_0909.lean` — Direct compilation fails and exit_velocity_components contains a sorry for a conclusion not derivable from its current hypotheses; therefore the file has neither a kernel-checked proof nor zero active placeholders.
- `PhyXMiniProblems/problem_phyx_mini_0913.lean` — Direct Lean compilation fails at line 583 with `No goals to be solved` because `ring` follows a goal-closing `simp`.
- `PhyXMiniProblems/problem_phyx_mini_0933.lean` — Direct Lean compilation fails at the two mul_lt_mul applications on lines 480 and 484 due to decimal-versus-rational pi-bound type mismatches.
- `PhyXMiniProblems/problem_phyx_mini_0940.lean` — The supporting arbitrary-unit lemma does not elaborate at the two coerced-zero rewrites, and therefore the target theorem is not directly compilable.
- `PhyXMiniProblems/problem_phyx_mini_0943.lean` — Direct Lean compilation fails at lines 426, 430, and 434 because `rw ... at _laws.<field>` requires a local hypothesis reference, not a projected term.
- `PhyXMiniProblems/problem_phyx_mini_0950.lean` — Direct Lean compilation fails, so the proof and its downstream numerical answer-choice conclusions are not verified.
- `PhyXMiniProblems/problem_phyx_mini_0952.lean` — The helper lemma `force_on_each_side` does not compile: fragile `congr 1` followed by `ring` leaves unresolved coordinate/zero-factor goals, so `problem_phyx_mini_0952` cannot be accepted as proved.
- `PhyXMiniProblems/problem_phyx_mini_0967.lean` — The file fails the required zero-active-sorry check: `finiteApparatusTorqueMagnitudeErrorBound` ends in `sorry`. Its present contract is under-specified because `RotatingCylinderDiskSetup.idealMagneticTorqueMagnitude` and `.idealMagneticTorqueVector` are independent fields, while the sole approximation hypothesis supplies no equality between them.
- `PhyXMiniProblems/problem_phyx_mini_0970.lean` — Direct Lean compilation fails at lines 416 and 489, so the helper lemmas and downstream theorem are not accepted.
- `PhyXMiniProblems/problem_phyx_mini_0971.lean` — There are two blockers: a local multiplication-order elaboration error at line 382, and a substantive missing signed-force measurability/integrability premise at line 406, where an active sorry admits the kick-speed limit used by the target theorem.
- `PhyXMiniProblems/problem_phyx_mini_0978.lean` — The proof does not compile. Its integrating-factor derivative and one-dimensional `Time` fderivative/interval transport steps use APIs or tactic shapes rejected by the current environment.
- `PhyXMiniProblems/problem_phyx_mini_0980.lean` — Direct Lean compilation fails in the three IntervalIntegrable continuity/congruence applications at lines 432, 438, and 445.
- `PhyXMiniProblems/problem_phyx_mini_0991.lean` — Direct Lean compilation fails in both integrating-factor proofs, so the downstream battery lemma and reviewed theorem are not verified declarations.
