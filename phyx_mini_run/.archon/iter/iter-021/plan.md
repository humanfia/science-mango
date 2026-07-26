# Iteration 021 Plan

## Batch contract

- Preserve exactly the 17 loop-selected Current Objectives below, in their
  existing order. All are mandatory proof-Review retries: `0825` and `0869`
  have used 2/3 reviewed attempts; the other 15 have used 1/3. No
  `proof_review_exhausted` target is present.
- Eligibility shortfall: 15. The fixed eligible set contains 17 distinct
  targets, so dispatch all 17 and leave the remaining 15 of the desired
  `max_parallel = 32` lanes unfilled; do not scan for or substitute targets.
- Preserve every theorem statement and physical hypothesis. Prefer exact
  scalar/vector identities before numerical bounds, prove every cancellation
  denominator and absolute-value branch, and keep under-hypothesized frozen
  lemmas honestly partial.
- The supplied excerpts expose no concrete blueprint chapter strategy defect,
  so no blueprint chapter is edited. In particular, `0869`, `0909`, `0967`,
  and `0971` have Lean-local frozen-statement or missing-hypothesis gaps; do not
  disguise them by changing the supported physical account.

## Per-target proof strategy

1. **`PhyXMiniProblems/problem_phyx_mini_0825.lean` (retry; 2/3 used).**
   Re-elaborate the rolling derivation by multiplying the rotational law by
   the radius, rewriting no-slip acceleration, and cancelling the explicitly
   nonzero radius. Combine the resulting friction/acceleration identity with
   tangential Newton's law to obtain the signed `-(2/7) M g sin β` value.
   Prove `0 < sin β` from the acute-angle hypotheses, select the nonpositive
   absolute-value branch, and normalize by `ring`.

2. **`PhyXMiniProblems/problem_phyx_mini_0869.lean` (retry; 2/3 used).**
   Compute the two graph integrals directly: the constant rectangle contributes
   `400` and the descending triangle contributes `100`, hence the total field
   integral is `500`. Use the potential-difference law and stated origin
   potential to prove the supported `V(3) = -200` target and discharge the
   displayed-choice result without routing through the false auxiliary
   `500 = 150`. The frozen auxiliary integral conclusion is inconsistent with
   the graph and must retain an explicit `sorry`.

3. **`PhyXMiniProblems/problem_phyx_mini_0897.lean` (retry; 1/3 used).**
   Rewrite the Coulomb-law component equations with the exact charge,
   displacement, distance, and constant calibrations; normalize each source
   force and then its superposed rational components. Square the norm, use
   `Real.sq_sqrt` and norm nonnegativity to certify the narrow magnitude
   interval, then split all four choices and prove the required absolute-value
   signs from those bounds before linear arithmetic.

4. **`PhyXMiniProblems/problem_phyx_mini_0898.lean` (retry; 1/3 used).**
   Expand the two-element source sum explicitly, rewrite all calibrated
   Coulomb data, and establish the exact resultant vector coordinatewise.
   Use `EuclideanSpace.norm_sq_eq`, the nonnegative norm, and `nlinarith` to
   prove `174/10^6 < ‖F‖ < 175/10^6`. Derive the rounding predicate and
   uniqueness by finite choice cases with separately justified `abs` branches.

5. **`PhyXMiniProblems/problem_phyx_mini_0909.lean` (retry; 1/3 used).**
   Project electric-force, Newton, and velocity-update laws onto both axes and
   cancel the positive electron mass. This closes the vertical exit-velocity
   formula and yields the general horizontal update containing the horizontal
   electric-field component. The frozen horizontal-velocity equality cannot
   follow because no hypothesis sets that component to zero; leave precisely
   that gap explicit, and do not use it to claim closure of dependent angle
   results.

6. **`PhyXMiniProblems/problem_phyx_mini_0913.lean` (retry; 1/3 used).**
   Recompute the two Coulomb field vectors and their superposition, reduce the
   resultant norm square to the exact rational value, and combine its lower
   and upper square comparisons with norm nonnegativity to obtain the
   `7550`–`7650` interval. Transfer it through the magnitude-readout equality,
   prove the `< 50` rounding error, and handle uniqueness by four finite cases
   with explicit distance signs.

7. **`PhyXMiniProblems/problem_phyx_mini_0933.lean` (retry; 1/3 used).**
   First normalize Faraday's law and the circular-coil geometry to the exact
   expression proportional to `π sin (π/36)`. Bound the small-angle sine using
   `sin x < x`, `sin x > x - x^3/4`, and certified rational bounds on `π`;
   propagate these to `245/10^6 < emf < 1/4000`. Use that interval to prove
   choice B's tolerance and strict separation from A, C, and D.

8. **`PhyXMiniProblems/problem_phyx_mini_0940.lean` (retry; 1/3 used).**
   Derive the ideal toroid formula in arbitrary units from flux linkage,
   uniform flux, and Ampère's mean-path law. Obtain nonzero current and radius
   readouts from physical positivity plus positive unit scales, clear only
   those certified denominators, and specialize to SI before rewriting the
   vacuum-permeability calibration. Retain the answer labels solely as
   metadata because no numerical `N`, `A`, or `r` is supplied.

9. **`PhyXMiniProblems/problem_phyx_mini_0943.lean` (retry; 1/3 used).**
   Rewrite the displayed `2 mA` current as exactly `1/500 A` and the three
   voltage calibrations as `4 V`, `4 V`, and `1 V`. Apply the inductor,
   capacitor, and source RMS laws separately to derive `X_L = 2000 Ω`,
   `X_C = 2000 Ω`, and `|Z| = 500 Ω`; finish the nested conjunction by
   unfolding only the recorded answer and displayed-magnitude definitions.

10. **`PhyXMiniProblems/problem_phyx_mini_0950.lean` (retry; 1/3 used).**
    Normalize the net-force law and readouts to the exact negative-`y` vector
    with magnitude `(8151/100000) π √3`. Certify tight `√3` and `π` bounds to
    place the magnitude between `0.443527` and `0.443529`, then use positivity
    for `norm_smul`, the direction witness, and the signed axial readout.
    Prove displayed match and unique closest choice by exhaustive `abs` signs.

11. **`PhyXMiniProblems/problem_phyx_mini_0952.lean` (retry; 1/3 used).**
    Obtain all four side-force identities, rewrite the finite side sum, and
    prove cancellation coordinatewise (`ext`/`fin_cases`/`ring`) if the
    existing `module` normalization remains brittle. Establish positivity of
    `I B₀ L`, use the unit-axis norm to compute the magnitude, and provide that
    positive scalar as the negative-`y` direction witness.

12. **`PhyXMiniProblems/problem_phyx_mini_0967.lean` (retry; 1/3 used).**
    In the main theorem, use the magnetic-dipole torque law to identify the
    stored ideal magnitude with the ideal vector norm, then combine
    `abs_norm_sub_norm_le`, the remainder decomposition, and its norm bound to
    transfer the finite-apparatus error. Normalize the ideal torque expression
    and separate choice B from the dimensionally defective alternatives. The
    standalone error lemma lacking the dipole-law hypothesis cannot make that
    norm replacement and must remain honestly partial.

13. **`PhyXMiniProblems/problem_phyx_mini_0970.lean` (retry; 1/3 used).**
    Rewrite the uniform shell's angular momentum and magnetic moment along
    `zHat`, evaluate a single coordinate, and cancel the strictly positive
    mass-radius-angular-speed coefficient to obtain `γ = Q/(2M)` in every
    unit system. At SI, compare this with the `g`-factor law, clear the
    positive mass denominator, and cancel the nonzero charge to get `g = 1`;
    rule out A, C, and D by the same nonzero-charge argument.

14. **`PhyXMiniProblems/problem_phyx_mini_0971.lean` (retry; 1/3 used).**
    Keep the established kick-speed/force-integral equality for positive
    separation ratios and compute the reference RC impulse with the exponential
    current profile and `integral_exp_mul_Ioi`. The available assumption only
    gives integrability after absolute value and does not supply measurability
    of the signed actual force, so the comparison of Bochner integrals—and
    therefore the limiting speed theorem—must retain its single explicit gap.

15. **`PhyXMiniProblems/problem_phyx_mini_0978.lean` (retry; 1/3 used).**
    Re-establish the exact center-field current estimate from the coupled-coil
    laws, then prove the needed exponential and prefactor bounds using the
    supplied certified `π` and `exp (-1)` inequalities. Convert the 1% relative
    current-error hypothesis into two linear inequalities, derive the observed
    milliampere interval, and prove answer B uniquely nearest by finite cases
    with explicit signs for each absolute value.

16. **`PhyXMiniProblems/problem_phyx_mini_0980.lean` (retry; 1/3 used).**
    Integrate the piecewise graph to its exact current-time area, multiply by
    the quarter-ohm resistance through Ohm's law, and apply integrated Faraday
    to the four-turn coil. Rewrite the `0.8 cm` radius and circular area, clear
    the nonzero `π` denominator, and derive exactly `3375/(256π) T`. Preserve
    the recorded `3.7 T` answer only as metadata because it conflicts with the
    modeled graph, whose value is approximately `4.196 T`.

17. **`PhyXMiniProblems/problem_phyx_mini_0991.lean` (retry; 1/3 used).**
    Introduce local scalars for `E`, `R₁`, `R₂`, `L`, `C`, `t` and the two
    exponential factors. Rewrite the battery-current and steady-state-current
    laws, certify positive `E`, `R₁`, and `R₂`, and clear only those nonzero
    resistance denominators. In each direction, rearrange to
    `E * (2 R₁ B - R₂ (2 A - 1)) = 0` and cancel the nonzero source emf to
    obtain the stated parameter-dependent transcendental equivalence.
