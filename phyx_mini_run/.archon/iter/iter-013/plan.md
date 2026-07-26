# Iteration 013 Plan

## Batch contract

- Dispatch exactly the 32 preselected new objectives below, in their existing
  order. Retry targets: 0; `proof_review_exhausted` targets: 0.
- Eligibility shortfall: 0; the full `max_parallel = 32` batch is occupied.
- Preserve every theorem signature and physical hypothesis. Derive all
  numerical conclusions from the governing laws. For transcendental
  readouts, first obtain an exact symbolic formula, then prove rational
  intervals for `pi`, `sqrt`, `sin`, `cos`, `tan`, `arcsin`, or `arccos`;
  never introduce a decimal approximation as a premise.
- No listed blueprint chapter needs correction: the supplied excerpts contain
  no concrete proof-strategy defect.

## Per-target proof strategy

1. **`problem_phyx_mini_0065.lean`.** Specialize the lensmaker law to
   centimeter units, rewrite the `40 cm`, air-index, and polystyrene-index
   readouts, and use the physical nonzero facts to clear denominators and
   solve `1 / f = 59 / 4000`. For the target, reuse the exact helper, unfold
   choice C and `MatchesAnswerToNearestCentimeter`, and close
   `|4000/59 - 68| ≤ 1/2` by rational normalization.

2. **`problem_phyx_mini_0066.lean`.** Rewrite either principal-focus distance
   with the figure coordinates to obtain `|f| = 40`. In the target, obtain
   `f < 0` from the biconcave/diverging classification and the focus law, turn
   the absolute-value equality into `f = -40`, and unfold the exact choice-C
   predicate.

3. **`problem_phyx_mini_0067.lean`.** Specialize the thin-lensmaker equation
   to centimeters and rewrite the signed `30 cm`/`40 cm` radii and
   polystyrene/air indices; clear the physically nonzero denominators to get
   `1/f = 1/200`, hence `f = 200`. Reuse that equality in the target, case-split
   the four answer labels and `norm_num` each mismatch, then unfold the
   recorded choice to prove its negation.

4. **`problem_phyx_mini_0068.lean`.** Prove the route-set equality by
   extensionality: unfold the finite-mirror route predicate, split the
   reflection cases, substitute the figure coordinates, and discharge the
   finite-segment inequalities and vector equalities coordinatewise. Transfer
   it through `image_seen_iff_visible_specular_route`; then rewrite the seen
   set to the explicit three-point insert set and compute `Set.ncard`, proving
   the three `![x,y]` points pairwise distinct by `simp`/`norm_num`.

5. **`problem_phyx_mini_0069.lean`.** Unpack the two specular-reflection laws
   and the depicted mirror/bisector directions. Evaluate the two reflection
   transforms successively, using the physical nonzero/unit-direction facts
   to normalize the vectors, and identify the outgoing direction with the
   explicit direction whose acute angle from the downward bisector is
   `20°`. Unfold `phiRadians` and `degreesToRadians`, then use the
   inner-product-angle branch bounds to conclude the required angle equality.

6. **`problem_phyx_mini_0070.lean`.** Obtain the centimeter relation directly
   by specializing the straight-sightline law and rewriting the figure angle
   and tank height. Rewrite `tan (pi/6)` to its exact square-root value and
   use positivity to solve the relation as `bottomRun = 50 * sqrt 3`; certify
   `86.5 < 50 * sqrt 3 < 87.5` by squaring rational bounds for `sqrt 3`.
   Unfold both rounding predicates so the same interval proves both conjuncts.

7. **`problem_phyx_mini_0071.lean`.** Derive the depth formula from the
   right-triangle product law by proving the acute-angle tangent nonzero and
   dividing. For the selection lemma, combine grazing Snell with the
   water/air readouts to fix the incidence sine, rewrite
   `tan (arcsin x)` to its algebraic square-root form on the physical branch,
   and prove the resulting depth lies in `[55,65]` using rational square-root
   bounds. Reuse the formula and unfold answer C in the target.

8. **`problem_phyx_mini_0072.lean`.** Expand `IsLeast` into threshold
   membership and a lower-bound obligation. For membership, instantiate the
   side-A Snell/geometry data at the critical ray; for an arbitrary admissible
   entry, use acute-branch monotonicity of `sin`, `arcsin`, and `tan` together
   with the side-B critical inequality to prove it is no smaller than the
   threshold. For choice C, eliminate the critical angle via its Snell law,
   reduce the threshold to an algebraic square-root ratio, and certify the
   `18.2 ± 0.05` interval by squared rational bounds.

9. **`problem_phyx_mini_0073.lean`.** Use normal violet emergence and Snell's
   law to determine the violet index, apply the `2%` dispersion relation to
   the red index, and combine the two face laws with the prism-angle relation
   to obtain an exact nested `arcsin` expression for `phi`. On the certified
   principal branches, bound that expression between the half-degree
   endpoints for `1°`; then case-split the other three labels and use the
   stronger interval bounds to prove strict uniqueness of choice C.

10. **`problem_phyx_mini_0074.lean`.** Prove the internal-angle helper by
    rewriting the `60°` apex and solving the equality-plus-sum equations;
    use angle branch facts only to normalize the degree coercions. Substitute
    the resulting `30°` entry refraction into entry-face Snell, rewrite
    `sin 30° = 1/2`, and obtain the exact index expression from the depicted
    incidence angle and air index. Certify its nearest-hundredth interval
    around `1.58` and prove choice C uniquely nearest by finite cases.

11. **`problem_phyx_mini_0075.lean`.** The trend law and `2 mm < 3 mm`
    readouts directly give the diffraction limitation. In the target, unfold
    the `let`, use Rayleigh's law to identify `theta`, use the exact centered
    geometry to rewrite the minimum circle diameter, and specialize the
    controlled cubic remainder at that `theta`; discharge its validity-radius
    premise from the regime hypothesis and multiply the bound by the positive
    chart distance. Keep the wavelength symbolic throughout.

12. **`problem_phyx_mini_0076.lean`.** Specialize the parallel-ray law to
    centimeters: the diverging lens places the virtual source `10 cm` left
    of the lens, while the mirror is `20 cm` to its right, so unfold the
    signed-distance readouts and solve the object distance as `30 cm`.
    Specialize the mirror equation with `f = 10` and `dₒ = 30`, solve
    `10(30+dᵢ)=30dᵢ` for `dᵢ=15`, and unfold choice C.

13. **`problem_phyx_mini_0077.lean`.** Specialize the universal round-trip
    imaging law to slopes `0` and `1`, unfold the ray-transfer computation and
    figure readouts, and subtract the equations to solve the common return
    plane as `30 cm`. Substitute that distance back into the zero-slope
    equation to obtain signed height `-8/3`; use the depicted inverted
    orientation and positive height magnitude to recover physical height
    `8/3`. Assemble the target and prove the `2.7 ± 0.05` choice-C test by
    rational normalization.

14. **`problem_phyx_mini_0079.lean`.** Analyze the admissible Bragg orders
    using positivity and `|sin θ| ≤ 1`, showing that the larger
    counterclockwise maximum is order four; choose the stated `arcsin`
    expression as witness and verify its geometry and Bragg-law clauses.
    Rewrite all readouts in the target, then certify the rotation lies within
    `37.8 ± 0.05°` using principal-`arcsin` and `pi` interval bounds; unfold
    choice C for the duplicate match conjunct.

15. **`problem_phyx_mini_0080.lean`.** Derive `18.8°` by combining the shown
    top-face angle with the `45°` diagonal-plane inclination. Use first-order
    Bragg, `d = a₀ / sqrt 2`, positivity of the glancing sine, and
    `sqrt 2 ≠ 0` to isolate the stated unit-cell formula. After rewriting the
    formula and readouts, certify `569.5 < 1000*a₀ < 570.5` to evaluate
    `round` as `570`, and case-split the choices to prove C strictly closest.

16. **`problem_phyx_mini_0081.lean`.** Specialize the longer-line,
    first-order Bragg law at the second graph peak, rewrite the `0.94 nm`
    spacing and angle interval, and bound `sin` on the physical branch to
    prove the `37 pm < λ < 40 pm` helper. In the target, unfold
    `IsUniqueClosestDisplayedAnswer`, case-split `other`, and use that interval
    with `abs` inequalities to show `38` beats `30`, `35`, and `25`;
    evaluate the displayed C value by `norm_num`.

17. **`problem_phyx_mini_0082.lean`.** At an arbitrary constructive order,
    rewrite the Fraunhofer law with the fringe equation and aperture/slit
    calibration to obtain phases `m*pi/4` and `m*pi`. Specialize at orders one
    and two, expand `Real.sinc`, and use the exact values at `pi/4`, `pi/2`,
    and integer multiples of `pi` to derive `56/pi^2` and `28/pi^2`.
    Prove the two display tolerances from certified rational bounds on `pi²`,
    then assemble the exact equalities and choice-C predicate.

18. **`problem_phyx_mini_0084.lean`.** Rewrite both interface phase readouts
    to one half-turn, so their integer difference is zero. Specialize the
    interference and optical-path laws to the third band in nanometers,
    substitute order three, `λ = 475`, and `n = 1.20`, and clear the positive
    denominator to get `t = 2375/4`. Reuse that helper and prove
    `round (2375/4) = 594` from the adjacent half-integer bounds.

19. **`problem_phyx_mini_0086.lean`.** Combine the critical-angle law,
    axial-projection law, in-core speed `c/n₁`, and constant-speed travel
    equations to eliminate both route lengths and times, yielding the stated
    exact delay formula. In the target, rewrite the `300 m`, `1.58`, `1.53`,
    exact Physlib light-speed, and seconds-to-nanoseconds readouts; reduce the
    result to a rational number and prove choice C closest by four finite
    cases and `norm_num`.

20. **`problem_phyx_mini_0087.lean`.** Substitute the primary-figure
    coordinates into the two distances to `P₁` and prove equality by
    coordinatewise norm-square simplification. Compute both `P₂` distances
    similarly and use the positive wavelength readout to prove their
    normalized difference is `16/5`. Expand propagation at `P₁` to calibrate
    the emission-phase offset, then expand it at `P₂`; cancel the nonzero
    wavelength and simplify `16/5 - 3/10 = 29/10`.

21. **`problem_phyx_mini_0088.lean`.** At the first graph minimum, combine
    zero intensity with positive single-ray intensity to get cosine `-1`;
    use the first-minimum phase interval and linear path law to select the
    half-cycle branch and prove optical path `λ/2`. Scale the linear
    optical-path relation from the calibrated minimum to `L = 1200 nm`,
    obtaining `4λ/5`, and substitute it in the phase law to get `8*pi/5`.

22. **`problem_phyx_mini_0089.lean`.** Use the dark-fringe readout,
    positivity, and the interference law to get cosine `-1`, then use the
    graph's first-fringe bounds and the linear path/phase laws to select
    phase difference `1/2` at `n = 7/5`. Substitute that calibration into the
    optical-path law and cancel the positive wavelength to prove
    `L = 5λ/4` in every unit system. Finally evaluate the same laws at `n=2`
    to obtain phase difference `5/4` and unfold choice C.

23. **`problem_phyx_mini_0090.lean`.** Substitute the depicted coordinates
    into the Euclidean path laws, divide by the positive common wavelength,
    and use `Real.sq_sqrt` to establish normalized lengths `sqrt 712` and
    `sqrt 436`. Subtract them for the path-difference helper and insert that
    result into the monochromatic propagation law after canceling equal source
    phases. For the target, bound both square roots tightly enough to place
    their difference in the nearest-choice cell around `5.80`, then discharge
    all competing choices by finite cases.

24. **`problem_phyx_mini_0091.lean`.** Rewrite the surface-referenced `65°`
    label and the complementary-angle law to solve the material-X normal
    angle as `25°`. For the target, use the water-air Snell equation with the
    `48°` water angle and standard indices to identify the air-angle sine;
    invert sine on the certified principal branch, prove the air angle is
    within half a degree of `82°`, and case-split the remaining labels to show
    answer A has strictly smaller radian error.

25. **`problem_phyx_mini_0092.lean`.** Rewrite equal path lengths, the
    material speed law, both constant-speed travel equations, and the arrival
    delay relation; clear the positive block length and light speed to derive
    `n = 1 + c*Δt/L`. In the target, substitute `L = 2.50 m`,
    `Δt = 6.25 ns`, and Physlib's exact `c`, normalize the unit conversions,
    and prove the resulting rational index differs from `1.75` by at most
    `0.005`.

26. **`problem_phyx_mini_0094.lean`.** Use the aligned first axis in Malus's
    law and `cos 0 = 1` to prove the first polarizer preserves irradiance.
    Substitute that equality and the requested detector ratio into the second
    Malus equation, cancel the strictly positive incoming irradiance, and get
    `cos² phi = 1/10`. On the acute branch, choose the nonnegative square root
    and use injectivity of cosine on `[0,pi]` to obtain the exact `arccos`
    solution; certify its `71.6 ± 0.05°` interval with rational cosine/square-
    root bounds and assemble the three conjuncts.

27. **`problem_phyx_mini_0095.lean`.** Unpack the line-shift geometry and
    primary scale readouts to express the water and air ray angles by their
    right-triangle sine ratios. Substitute those expressions into Snell's law,
    using the physical positivity facts to clear the square-root denominators,
    and derive a tight rational interval for the water index centered at
    `1.3`. The interval proves the `< 1/20` first conjunct; case-split all
    other choices and compare absolute errors to establish unique closeness.

28. **`problem_phyx_mini_0096.lean`.** Unfold the admissible TIR set. Show the
    predicted critical ray is admissible by the critical Snell equality, and
    for any admissible incidence use the perpendicular-face complement,
    physical angle bounds, and monotonicity of sine/arcsine to prove it does
    not exceed the candidate. For the display helper, rewrite `n = 1.38`,
    reduce the critical cosine to a square-root expression, and certify the
    predicted angle lies within the explicit `0.15°` tolerance of `72.1°`;
    combine the two helpers in the target.

29. **`problem_phyx_mini_0097.lean`.** Use the right-angle prism geometry to
    identify incidence at A as `50°`. The critical law at A gives
    `n_glass*sin 50° = n_air`; eliminate those indices from entry-face Snell
    to obtain `sin thetaA = sin 40° / sin 50°`. Apply the physical
    `[0,pi/2]` branch facts to rewrite `arcsin (sin thetaA)` back to `thetaA`,
    then normalize the `Real.Angle` coercions.

30. **`problem_phyx_mini_0098.lean`.** Square the entrance Snell equation,
    use the `90°` complement to replace the core-axis sine by the
    core-cladding cosine, and combine the critical Snell law with
    `sin²+cos²=1` to prove the numerical-aperture identity. Rewrite the air,
    core, and cladding index readouts in that identity; on the acute branch
    take the positive square root and certify the resulting arcsine lies
    within `12.1 ± 0.05°` using rational `sqrt`, `sin`, and `pi` bounds.

31. **`problem_phyx_mini_0099.lean`.** Unpack the symmetric prism geometry
    and the two face Snell laws, solve each emergent angle on its physical
    branch as `arcsin (n_prism/n_air * sin A)`, and use symmetry to rewrite
    the separation as twice the single-ray deviation. Substitute
    `n = 1.66` and `A = 25°`, then certify the exact symbolic expression lies
    strictly between the degree endpoints `39.05°` and `39.15°`.

32. **`problem_phyx_mini_0100.lean`.** Derive the `60°` hypotenuse incidence
    from normal entry and the `30-60-90` geometry. Unfold the critical-index
    candidate, rewrite `sin(pi/3)=sqrt 3/2` and `sin(pi/2)=1`, and use
    `WithDim` extensionality to obtain `39*sqrt 3/50`. For `IsGreatest`,
    unfold admissibility, prove the boundary member from the physical/TIR
    inequalities, and bound every admissible liquid index by critical Snell
    monotonicity. Finally bound `sqrt 3` rationally and case-split the choices
    to prove `1.35` uniquely closest.
