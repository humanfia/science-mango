# Iteration 005 prover plan

Bounded scope: exactly the two mandatory Proof Review retries below, in the
supplied order. Preserve all theorem statements and physical hypotheses. The
six experimental E1 targets remain user-skipped, not failed.

1. **`IPhO2026Problems/problem_IPhO_2026_1_C_1.lean`**
   - Keep the existing energy-conservation reduction and the proof that the
     photon-momentum magnitude is strictly positive.
   - For the remaining kinetic-energy identity, unfold only the two kinetic
     energy definitions, use momentum conservation to replace the oxygen-atom
     momentum by the photon momentum minus the oxygen-molecule momentum, and
     rewrite the photon vector as its scalar magnitude times the incident
     direction.
   - Expand the resulting squared norm. Use `norm_smul` together with
     `abs_of_pos hPhotonMomentum`, the unit incident-direction law, and the
     Figure 1c inner-product/angle law to obtain the radial quadratic. Normalize
     the scalar expression with `ring_nf`/`ring`; clear mass denominators only
     with the positive oxygen-mass field from `hParameters`.
   - Compile the file and confirm that the sole `sorry` is removed without
     changing the revised `Parameters.Valid` contract.

2. **`IPhO2026Problems/problem_IPhO_2026_2_B_1.lean`**
   - Compile the already closed file unchanged first; this retry has no open
     placeholder.
   - Check the final theorem's dependency chain: the attained maximum,
     `MaximalRayTangencyLaw`, and the optics model must feed
     `maximum_ray_containerRadius_eq_limitingRadius`, which then feeds
     `limitingRadiusMeters_eq_trigFormula`.
   - Retain the explicit witnesses `alpha = R` and `beta = -R/2`; the final
     `scaledLength` normalization should remain a local `simp` plus `ring`.
     If elaboration has drifted, repair only the affected theorem application
     or normalization, never the statement or its physical hypotheses.
   - Confirm clean compilation and no proof escape hatch, then route the
     unchanged proof back to Proof Review.

No supplied blueprint excerpt has a concrete strategy defect, so no blueprint
chapter correction is planned.
