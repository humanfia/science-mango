# Iteration 012 Plan

## Batch contract

- Dispatch exactly the 32 preselected new objectives below, in their existing
  order. Retry targets: 0; `proof_review_exhausted` targets: 0.
- Eligibility shortfall: 0; the full `max_parallel = 32` batch is occupied.
- Preserve every theorem signature and physical hypothesis. Derive numerical
  answers from the governing laws; for trigonometric readouts, prove explicit
  rational intervals rather than assuming decimal approximations.

## Per-target proof strategy

1. **`problem_phyx_mini_0028.lean`.** Unpack the two spherical-exit laws and
   the physical branch conditions, specialize the lens/readout data, and solve
   the surface coordinates and normal angles for each height. Use Snell's law
   on the certified principal branches to rewrite the two transmitted angles,
   then substitute the crossing formulas. Clear only denominators proved
   nonzero from the angle bounds, and certify the final strict `21.3 ± 0.05`
   interval with rational bounds for `pi`, `sqrt`, `sin`, and `tan`.

2. **`problem_phyx_mini_0029.lean`.** For the helper, unfold the readouts,
   eye-plane placement, virtual-image condition, and thin-lens equation;
   normalize the signed distances and use `field_simp` with their explicit
   nonzero proofs to obtain `1/f = 2/3`. In the target, rewrite the optical
   power law with that helper, give integer witness `667` for the thousandth
   readout, and close the absolute-value inequality by `norm_num`.

3. **`problem_phyx_mini_0031.lean`.** Specialize both thin-lens laws to the
   centimeter units and unpack the readout and axial-geometry equalities.
   Prove all denominators nonzero from the physical placement, clear them, and
   solve successively for the second signed image distance, second object
   distance, intermediate position, and finally `p = 785/59`. Reuse the two
   helpers in the target and discharge the nearest-tenth bound by `norm_num`.

4. **`problem_phyx_mini_0032.lean`.** Unfold the mirror/lens readouts,
   stage-connection geometry, and paraxial laws. Clear the nonzero physical
   distances and solve the mirror stage (`10`, `25/2`, `50`, `-4`) and return
   lens stage (`-25`, `-4175/83`, `-167/83`) with `ring_nf`/`nlinarith`.
   Multiply the two stage magnifications to get `668/83`; normalize the
   distance from `8.05` to prove the hundredth tolerance.

5. **`problem_phyx_mini_0033.lean`.** Unpack the plane-face law and figure
   data to obtain zero in-glass vergence and zero axial angle. Substitute the
   zero vergence, indices, and signed radius into the spherical-face equation;
   use physical positivity to clear the focus-distance denominator and solve
   `q = 75/7`. Apply the helper in the target and prove the `10.7 ± 0.05`
   inequality by exact rational normalization.

6. **`problem_phyx_mini_0034.lean`.** Keep the division-free Gaussian and
   magnification equations throughout. First solve the direct lens path for
   `50/3` and `25`; substitute the common final-image geometry into the
   reflected lens law to prove the mirror intermediate image coincides with
   the object. Then solve the mirror equation for focal length `35/3` and
   derive the stage magnifications/product required by the final theorem.
   Close the `+11.7 cm` display (and any recorded-choice consequence in the
   omitted suffix) by exact rational arithmetic.

7. **`problem_phyx_mini_0036.lean`.** Extract the incident angle, reflection
   equality, refractive indices, Snell equality, and acute/principal-branch
   bounds from the four hypotheses. Reflection gives `thetaR = 60°`; use
   injectivity of `sin` on the certified refracted branch to obtain the stated
   `arcsin` expression. Prove the `49.3°` tolerance by bounding the sine at the
   two degree endpoints and using monotonicity of `arcsin`, with certified
   rational `pi`/sine estimates.

8. **`problem_phyx_mini_0037.lean`.** From complete polarization and the
   Brewster criterion obtain `θr + θt = pi/2`; combine it with Snell's law and
   the acute angle bounds to derive the usual positive tangent/index-ratio
   characterization of `θr`. Bound this angle between `53.05°` and `53.15°`
   using strict monotonicity of `tan` on the acute interval and certified
   endpoint estimates, then unfold the readout predicate.

9. **`problem_phyx_mini_0038.lean`.** Specialize the mirror equation to
   centimeters, rewrite the two figure distances, prove their nonzeroness,
   and clear denominators to solve `f = 300/31`. In the target reuse the
   helper, provide integer witness `968`, and prove the hundredth-error bound
   by `norm_num`; the sign and radius hypotheses remain available but need not
   be used.

10. **`problem_phyx_mini_0039.lean`.** Unpack the rational figure readouts and
    paraxial mirror laws, then solve the division-free mirror equation for
    `s' = -225/128`. Substitute this into the transverse-magnification/height
    equation to obtain `y' = 15/4`. The target follows from the height helper;
    unfold the half-open rounding bin and verify that `3.75` lies in the
    choice-B interval by `norm_num`.

11. **`problem_phyx_mini_0040.lean`.** Linearize the exact vertex Snell
    residual using the supplied `HasDerivAt` hypotheses, rewrite the stated
    indices, radius, and object distance, and use uniqueness of derivatives to
    solve the resulting linear equation for image distance `304/27`. Repeat
    the derivative comparison for the transverse image map to force lateral
    magnification `-25/27`. For closest-choice uniqueness, rewrite the exact
    value, case-split the finite `AnswerChoice`, and close each rational
    absolute-value comparison with `norm_num`.

12. **`problem_phyx_mini_0041.lean`.** Combine the first-order spherical ray
    geometry with the derivative of exact Snell's law; simplify derivatives of
    `sin` at zero and compare derivative values to derive signed image distance
    `-64/3`. Apply the same derivative-uniqueness argument to the chief ray and
    optical-axis map to get magnification `7/3`. Rewrite the target with this
    value and prove the choice-B tolerance by rational `norm_num`.

13. **`problem_phyx_mini_0042.lean`.** Derive the generic apparent-depth
    formula by unpacking paraxial geometry and the linear Snell law, cancelling
    only slopes/nonzero depths justified by the physical hypotheses. Substitute
    the pool data to get `200/133`. Supply integer witness `15` for the
    nearest-tenth result and prove it plus all three rival comparisons by
    unfolding definitions, case-splitting `AnswerChoice`, and `norm_num`.

14. **`problem_phyx_mini_0043.lean`.** Specialize the two lens equations,
    rewrite the source distances and axial connection, and solve successively
    for `qA = 24`, `pB = 12`, and `qB = 12`. Feed those values into the two
    transverse-magnification laws to obtain `mA = -2`, `mB = -1`, and propagate
    the signed heights to `IPrime = 16`; their product gives overall
    magnification `2`. Prove the omitted recorded-choice diagnostic from these
    exact values by direct simplification, accounting for the fourth
    placeholder without treating metadata as a premise.

15. **`problem_phyx_mini_0044.lean`.** Rewrite the signed object/image
    distances in the thin-lens equation and normalize to `1/f = 3/100`.
    Positivity of the physical focal length supplies `f ≠ 0`; clear the
    reciprocal equation to obtain `f = 100/3`. Unfold the answer predicate and
    prove its distance from `33` is at most `1/2` by `norm_num`.

16. **`problem_phyx_mini_0045.lean`.** Unfold the far-point placement and
    stated distances to derive the signed virtual-image distance `-48`.
    Instantiate the parallel-ray focal law using the object-at-infinity and
    parallel-incident-ray facts from the figure, specialize to centimeters,
    and rewrite with the helper. Both target conjuncts then reduce to
    `norm_num`.

17. **`problem_phyx_mini_0047.lean`.** Unpack the first-minimum geometry to
    derive the half-separation/right-triangle angle
    `arctan (((16/1000)/6))`. Specialize the Fraunhofer minimum law to the
    stated wavelength and first order, prove the sine denominator positive
    from the acute geometry, and solve symbolically for the slit width. Stop at
    the exact quotient in the theorem; do not try to prove any displayed
    nanometer choice.

18. **`problem_phyx_mini_0048.lean`.** For each boundary lemma, unfold the
    closet dimensions, boundary-height condition, and planar-reflection
    geometry, then solve the resulting similar-triangle equations for floor
    distances `1/4` and `4`. In the target unfold `floorStreakLength`, rewrite
    both helper results, and normalize to `15/4`; the choice-B equality is the
    same computation after unfolding `MatchesAnswerChoice`.

19. **`problem_phyx_mini_0049.lean`.** Rewrite the input elevation as a
    `60°` incidence angle from the normal. Use Snell at the entry and exit
    faces, equality of the two air indices, parallel-face geometry, and the
    physical angle intervals to equate the outgoing and incoming normal
    angles via injectivity of `sin` on the admissible branch. Unfold the
    choice-B readout to finish.

20. **`problem_phyx_mini_0050.lean`.** Derive the internal `30°` and outgoing
    `52.6°` angles directly from the prism geometry. Substitute them, together
    with air index one, into exit-face Snell; prove `sin 30° ≠ 0` and divide to
    obtain the exact quotient. Reuse that equality in the target and certify
    that the quotient lies within `1.59 ± 0.005` using
    `sin 30° = 1/2` and explicit rational bounds for `sin 52.6°`.

21. **`problem_phyx_mini_0051.lean`.** Prove the diameter formula from the
    critical-ray right triangle and diameter/radius relation. From critical
    Snell obtain `sin θc = 100/133`; use acute positivity and
    `sin² + cos² = 1` to express the positive tangent through
    `sqrt (133² - 100²)` without inverse trigonometry. Substitute the `3 m`
    depth and certify the `6.8 ± 0.05` interval with rational square-root
    bounds.

22. **`problem_phyx_mini_0052.lean`.** Specialize the thin-lens equation to
    centimeters, rewrite `f = 6` and `s = 4`, clear nonzero denominators, and
    solve `s' = -12`. Combine this with the axis-geometry equality for the
    displayed-location helper. Finally specialize the magnification law,
    rewrite `s`, `s'`, and obtain `m = 3`; `IsCorrectAnswer .B` then simplifies
    to the same equality.

23. **`problem_phyx_mini_0053.lean`.** Rewrite `f = -50` and `s = 100` in the
    signed lens equation and clear denominators to derive `s' = -100/3`.
    Substitute this result into the magnification law to get `m = 1/3`.
    In the target reuse the helper, give integer witness `33`, and prove
    `|1/3 - 33/100| ≤ 1/200` by `norm_num`.

24. **`problem_phyx_mini_0054.lean`.** Derive radius `2 cm` from the diameter
    readout and hemispherical geometry. Specialize the spherical-surface
    equation to centimeters, substitute `n1 = 1`, `n2 = 3/2`, object distance
    `6`, and radius `2`; use physical positivity for the image-distance
    denominator and solve `s' = 18`. Unfolding `MatchesAnswerChoice .B` leaves
    the same equality.

25. **`problem_phyx_mini_0055.lean`.** Differentiate the all-near-axis Snell
    equality at zero, simplify `sin 0`, `cos 0`, and compare the supplied
    incident, normal, and back-projection derivatives. Rewrite the fish,
    vertex, radius, and refractive-index readouts to solve the resulting
    rational linear equation for image distance `5000/599`. Then prove the
    choice-C tolerance and strict superiority over each rival by finite
    `AnswerChoice` cases and `norm_num`.

26. **`problem_phyx_mini_0056.lean`.** Unfold the directed-center geometry to
    establish the signed radii `-40` and `-20`. Specialize the lensmaker law to
    centimeters and rewrite those radii plus the glass/air indices to obtain
    reciprocal focal length `1/80`. Physical focal-length positivity gives
    nonzeroness; clear reciprocals to prove focal length `80`, then unfold the
    choice-C equality.

27. **`problem_phyx_mini_0057.lean`.** Derive zero first-face curvature and
    negative reciprocal second-face curvature from the plane/center geometry.
    The imaging equation with its distance readouts yields `1/f = 21/160`.
    Substitute both results and the glass/air indices into lensmaker's equation;
    radius positivity permits cancellation and gives `R = 80/21`. Reuse it in
    the target and prove the `3.8 ± 0.05` bound by `norm_num`.

28. **`problem_phyx_mini_0058.lean`.** Use the signed magnification law and
    readouts to solve `s' = -8`, then insert this in the Gaussian lens equation
    and clear denominators to obtain `f = 8/3`. The target's rounding interval
    is rational arithmetic. For unique closest choice, rewrite `f`, split the
    four answer constructors, eliminate the selected case, and use `norm_num`
    for the three strict comparisons.

29. **`problem_phyx_mini_0059.lean`.** Unpack the figure geometry and focal
    radius law, substitute them into the Gaussian mirror equation, and solve
    jointly with the signed magnification law for `s' = -40` and `m = 2`.
    Specialize the image-height law to centimeters and rewrite the `3 cm`
    object height to obtain image height `6`; `MatchesAnswer .C` unfolds to
    exactly that equality.

30. **`problem_phyx_mini_0062.lean`.** Obtain the reflected endpoints
    `±pi/3` from the regular-hexagon transition and doubled reflection angles.
    Substitute them into wall projection to prove the exact streak formula.
    Rewrite the wall distance and `0.2 m` vertex radius, reduce
    `tan (pi/3)` to `sqrt 3`, and prove choice C is nearest by the finite four
    cases using a certified rational enclosure for `sqrt 3` (for example
    `1.732 < sqrt 3 < 1.733`).

31. **`problem_phyx_mini_0063.lean`.** Unfold the reflected ceiling path to a
    straight ray toward the reflected wall midpoint, giving rise/run `9/10`.
    Use the acute-angle hypothesis and injectivity of `tan` on
    `(-pi/2, pi/2)` to identify the `Real.Angle` with the cast of
    `arctan (9/10)`. Establish that this representative lies between
    `41.5°` and `42.5°` by monotonicity of `tan` and certified endpoint
    trigonometric bounds; then unfold `degreeReadout` and the choice-C
    predicate.

32. **`problem_phyx_mini_0064.lean`.** Read the two center-arrow orientations
    to prove signed radii `+24` and `-40`. Substitute those and the glass/air
    indices into the lensmaker equation, normalize, and obtain `1/f = 1/30`.
    Use physical focal-length positivity to clear the reciprocal and conclude
    `f = 30`; both target conjuncts then follow after unfolding choice C.

## Blueprint corrections

None. The supplied excerpts contain no concrete strategy defect requiring an
edit to a listed blueprint chapter.
