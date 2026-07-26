# Iteration 017 Plan

## Batch contract

- Preserve exactly the 128 loop-selected Current Objectives below, in their
  existing order: three mandatory proof-Review retries followed by 125 new
  accepted-open targets. No `proof_review_exhausted` target is present.
- Eligibility shortfall: 0. The selected list exceeds `max_parallel = 32`;
  execution should keep 32 distinct lanes occupied while draining this fixed
  ordered list, with the three retries dispatched first. Plan does not mutate
  or truncate the loop-selected objectives.
- Preserve every theorem signature and physical hypothesis. Keep exact
  physical relations separate from finite-precision answer predicates, prove
  denominator and branch conditions explicitly, and certify radical,
  exponential, logarithmic, trigonometric, and rounding bounds.
- The supplied blueprint excerpts expose no concrete chapter-level strategy
  defect, so no blueprint chapter is changed.

## Per-target proof strategy

1. **`PhyXMiniProblems/problem_phyx_mini_0308.lean` (retry; 2/3 used).**
   Rebuild the cross-multiplied delay identity with a typed `calc` chain from
   `waterDelay`, `airCalibratedDelayDistance`, the bearing geometry, and the
   residual identity, avoiding fragile reverse `rw` across unit readouts.
   Subtract the ideal term by `ring`, rewrite the absolute product using the
   positive air speed, and scale the stated residual bound.

2. **`PhyXMiniProblems/problem_phyx_mini_0428.lean` (retry; 1/3 used).**
   Retain the derived heat/work readouts, but certify
   `x = 6^(2/3)` by `x > 0` and `x^3 = 36`; prove the rational lower and upper
   bounds by explicit cube comparisons and monotonicity rather than an
   under-justified square argument. Use those bounds to choose the `max`
   branches, cancel the positive `nR` factor in the efficiency, and close the
   two-decimal interval through reciprocal inequalities.

3. **`PhyXMiniProblems/problem_phyx_mini_0439.lean` (retry; 1/3 used).**
   Preserve the source-grounded symbolic conclusion. Specialize every
   mass-volume law to kilograms/metres, derive tank A's mass `2`, tank B's
   volume `(7/2)v_B`, total mass `11/2`, and total volume
   `1 + (7/2)v_B`; then use the final mass-volume law and `linarith`. Do not
   infer choice D from an absent water-property table.

4. **`PhyXMiniProblems/problem_phyx_mini_0490.lean`.**
   Rewrite the speed, heat-capacity, energy-loss, and temperature-rise laws to
   derive `17/120` by `field_simp`/`ring`. Unfold both answer predicates,
   enumerate the four choices, and discharge the `0.14` rounding and strict
   closest-choice inequalities with `norm_num`.

5. **`PhyXMiniProblems/problem_phyx_mini_0491.lean`.**
   First unfold the Physlib pressure units to prove the standard-atmosphere
   conversion. For each process helper, rewrite the figure readouts and
   isobaric/isochoric work and first-law equations; normalize litre-atmosphere
   factors to joules, sum the two legs, and finish the exact heat and unique
   displayed-choice claims by finite case analysis.

6. **`PhyXMiniProblems/problem_phyx_mini_0492.lean`.**
   Specialize the boundary-work laws to SI, show the first leg contributes
   zero and the second gives
   `1.4 * (9.3 - 5.9) * 101.325 = 482.307 J`. Unfold the nearest-ten predicate
   and cases on the answer choice to prove D and uniqueness numerically.

7. **`PhyXMiniProblems/problem_phyx_mini_0493.lean`.**
   Rewrite the hot/cold temperature readouts in the Carnot law and normalize
   `1 - 77/293` to `216/293`. Substitute this into the target, prove the
   integer rounding of `21600/293` to `74`, and close the displayed D equality
   by reduction.

8. **`PhyXMiniProblems/problem_phyx_mini_0495.lean`.**
   Derive the process-B internal-energy change from the stated ideal-gas/first
   law readouts, keeping all positive scale factors until cancellation.
   Unfold the ten-joule matching predicate, split on all four choices, and use
   the exact rational value to prove the iff with D.

9. **`PhyXMiniProblems/problem_phyx_mini_0496.lean`.**
   Obtain `E = 500/0.01 = 50000 V/m`, eliminate transit time and velocity from
   the deflection and Lorentz-balance laws, and isolate the positive magnetic
   field as `sqrt (m ΔV/q)/L`. Square against rational endpoints using proton
   calibration and positivity to prove `45.5 < B_mT < 46.5`, then enumerate
   choices for rounding and closestness.

10. **`PhyXMiniProblems/problem_phyx_mini_0497.lean`.**
    Rearrange planar momentum conservation to the gold recoil vector, use the
    mass-number ratio and the norm-square/cosine identity, and take the
    nonnegative square root for the exact formula. Establish a certified
    interval around `2.52e5 m/s` using cosine bounds at the stated angle, then
    unfold the `500 m/s` tolerance and select C.

11. **`PhyXMiniProblems/problem_phyx_mini_0499.lean`.**
    Rewrite the two graph points and normalize their difference quotient to
    `4e-15 V s`. Subtract the two Einstein equations to cancel the work
    function, multiply by the `1.6e-19 C` calibration, and normalize to
    `6.4e-34 J s`, which definitionally matches choice C.

12. **`PhyXMiniProblems/problem_phyx_mini_0500.lean`.**
    Convert the raster pixel ratio to `200/3 μm`, then use the slit law to
    derive `40/21 fm`. Combine de Broglie with the standard neutron constants,
    prove the `1.5e8 ≤ v < 2.5e8` interval by positive-denominator arithmetic,
    and witness the one-significant-figure predicate with digit `2`, exponent
    `8`; do not claim the literal `200 m/s` metadata value.

13. **`PhyXMiniProblems/problem_phyx_mini_0501.lean`.**
    Use triangular normalization to determine peak density, integrate the
    linear branch over the narrow strip to get probability `1/900`, and apply
    the expected-count law to obtain `10000/9`. Unfold unique closestness,
    enumerate choices, and close the rational absolute-value comparisons.

14. **`PhyXMiniProblems/problem_phyx_mini_0502.lean`.**
    Rewrite the narrow-strip law with the central density `0.50` and width
    `0.010` to get `5/1000`. The main theorem then follows by unfolding
    `MatchesAnswerChoice`, reducing choice C, and applying the helper.

15. **`PhyXMiniProblems/problem_phyx_mini_0503.lean`.**
    Evaluate the piecewise-linear normalization integral to force the peak
    readout `1/4`; compute the two symmetric trapezoid areas as `3/4`.
    Substitute the result, unfold matching/uniqueness, and eliminate the four
    answer choices by `decide`/`norm_num`.

16. **`PhyXMiniProblems/problem_phyx_mini_0504.lean`.**
    Combine the bandwidth-period and 50%-duty period laws, cancel the positive
    period, and obtain maximum rate `bandwidth/2` in a common time unit.
    Rewrite `200 kHz` as `200000 Hz`, yielding `100000`, then unfold the
    recorded C match.

17. **`PhyXMiniProblems/problem_phyx_mini_0505.lean`.**
    Evaluate the figure-specified density integral over `[-0.30,0.30]` to
    `9/100`, then multiply by `10000` through the expected-count law. For the
    biconditional, split on each answer choice and normalize the displayed
    natural-number casts.

18. **`PhyXMiniProblems/problem_phyx_mini_0506.lean`.**
    Use the inside linear formula and zero-outside condition to rewrite both
    the global normalization integral and the central interval integral as
    polynomial interval integrals. Solve normalization for `c²`, obtain
    probability `1/8`, and prove its membership in the `0.13` rounding
    interval by `norm_num`.

19. **`PhyXMiniProblems/problem_phyx_mini_0507.lean`.**
    Algebraically eliminate fall time, speed, momentum, and wavelength to
    derive the exact squared-distance formula. Express the remainder as a
    relative perturbation, expand the difference of squares, and use its
    stated bound for `2η+η²`; separately certify the leading estimate interval
    and enumerate choices, without transferring the approximation to the
    physical distance.

20. **`PhyXMiniProblems/problem_phyx_mini_0508.lean`.**
    Extract mode `4` from the four-lobe figure law, substitute it into the
    infinite-well energy equation, and use positivity to isolate the box
    length. Prove the squared rational bounds corresponding to
    `|L_nm-1|<0.01`, then establish `round (10L)/10 = 1` and uniqueness by
    cases.

21. **`PhyXMiniProblems/problem_phyx_mini_0509.lean`.**
    Rewrite the proper length, `β = 0.990`, and length-contraction law to
    `400/γ(0.99)`. Reduce `γ` to a square-root expression and prove the result
    lies within `1/20` of `56.4` using certified square bounds; this directly
    closes the D predicate.

22. **`PhyXMiniProblems/problem_phyx_mini_0511.lean`.**
    Use threshold energy conservation and mass readouts to derive
    `γ β = 179/167`. Square the Lorentz-factor equation, select the nonnegative
    subluminal branch, and get `β = sqrt (1-(167/179)^2)`. Rewrite the
    dimensionful readout law and prove the `0.360` interval plus uniqueness by
    rational square bounds and choice cases.

23. **`PhyXMiniProblems/problem_phyx_mini_0512.lean`.**
    Normalize the velocity-addition law to fractions of `c` and derive
    `55/64`. Use the intercept law and positive light speed to obtain the exact
    flight-time quotient, then bound the Physlib light-speed readout tightly
    enough to prove D is strictly closest among the four times.

24. **`PhyXMiniProblems/problem_phyx_mini_0515.lean`.**
    Specialize Einstein's law at the zero-stopping threshold to prove
    `φ = hf₀`. Convert the graph intercept and reference constants to eV,
    derive the stated `0.4 eV` error around `4.8`, and enumerate choices to
    establish D is nearest.

25. **`PhyXMiniProblems/problem_phyx_mini_0516.lean`.**
    Subtract the fitted Einstein equations at two distinct frequencies and
    cancel the positive charge to prove `h = e·slope`. Evaluate the six-row
    least-squares sums exactly, insert `c` and `e`, and prove the resulting
    value falls in D's half-unit interval and no other choice's interval.

26. **`PhyXMiniProblems/problem_phyx_mini_0517.lean`.**
    Reduce all depicted level gaps from the figure and prove the direct
    `3 eV → 0` transition is uniquely largest by finite cases. Divide the
    Planck–Einstein laws by positive `h` to transfer strict gap order to
    frequency order, then certify the D-frequency rounding interval.

27. **`PhyXMiniProblems/problem_phyx_mini_0518.lean`.**
    Rewrite the three transition energies and ejection/non-ejection
    observations into inequalities on the work function. Show the actual
    readout belongs to the consistent set and that `5` is its greatest
    element; unfold the answer predicates and use the distinct displayed
    values to prove D uniquely represents that maximum.

28. **`PhyXMiniProblems/problem_phyx_mini_0519.lean`.**
    Use ionization data to determine the level-energy scale, compute the
    `n=4` to `n=2` energy gap, and solve the positive photon
    energy–wavelength product. Bound the resulting nanometre readout in
    `[377.5,378.5)` with certified constant arithmetic.

29. **`PhyXMiniProblems/problem_phyx_mini_0520.lean`.**
    Prove the asymptotic equivalence by rewriting `sinh x` with exponentials,
    factoring the dominant `exp (2x)` term, and applying standard exponential
    limits under `0<E<U₀`. Derive opacity from the dispersion law, evaluate
    exact and opaque coefficients separately, and keep their distinct
    numerical/choice conclusions explicit.

30. **`PhyXMiniProblems/problem_phyx_mini_0521.lean`.**
    Convert the exterior Schrödinger equation to the constant-coefficient ODE,
    define positive `κ` from the positive energy gap, and obtain the two
    exponential modes. Use the finite-at-infinity/Tendsto premise to eliminate
    the growing coefficient, shift the surviving exponential to the well
    boundary, and prove decay to zero.

31. **`PhyXMiniProblems/problem_phyx_mini_0522.lean`.**
    Expand the six Coulomb-pair terms using the collinear figure distances and
    equal dipole moments. Group the two internal attractive pairs, compute the
    inverse-cube far-field coefficient from the remaining four-pair profile,
    and substitute both helpers into the requested energy/answer formula while
    retaining the stated remainder regime.

32. **`PhyXMiniProblems/problem_phyx_mini_0524.lean`.**
    Project the classical velocity triangle and divide by positive `c` to
    obtain `sin φ=v/c`. Use the acute-angle branch and `arcsin_sin` to isolate
    `φ`; then bound `v/c` and `arcsin` via monotonicity/Taylor bounds tightly
    enough for D's `5e-8` interval, and eliminate other choices.

33. **`PhyXMiniProblems/problem_phyx_mini_0525.lean`.**
    Rewrite the attenuated reference, exact moving-reflector Doppler, and mixer
    laws with the supplied readouts. Clear positive denominators to prove the
    beat lies in `(2,2.005) kHz`; unfold the rounding/matching predicates and
    close both D claims from that interval.

34. **`PhyXMiniProblems/problem_phyx_mini_0526.lean`.**
    Divide the contracted longitudinal and invariant transverse projections,
    cancel the positive rod length, and use the acute orientations to derive
    `θ₀ = arctan (tan θ/γ)`. Certify `3.295° < θ₀ < 3.305°` with square,
    tangent, and arctangent bounds, then prove D nearest.

35. **`PhyXMiniProblems/problem_phyx_mini_0527.lean`.**
    Substitute the signed Earth-frame velocities into Einstein's transform,
    prove the enemy velocity is `-5/14` in the patrol frame, and use the
    magnitude premise for speed `5/14`. `norm_num` then proves the `0.357`
    rounding interval for D.

36. **`PhyXMiniProblems/problem_phyx_mini_0528.lean`.**
    Solve the two light and spacecraft worldline equations for
    `Δt_S=2d/(c+v)` with a positive denominator. Divide by the positive
    Lorentz factor via the proper-time law, insert the readouts, and prove the
    whole-second match and uniqueness by certified radical bounds.

37. **`PhyXMiniProblems/problem_phyx_mini_0529.lean`.**
    Solve the uniform ball trajectory in the moving frame, transform the two
    endpoint event times to the ground/Ed frame, and simplify the elapsed-time
    expression. Use the supplied speed and distance readouts with positive
    denominators to trap the duration within `5 s` of `4880`.

38. **`PhyXMiniProblems/problem_phyx_mini_0530.lean`.**
    Derive supplementary scattering angles from the opposite initial/final
    photon directions; rewrite `cos (π-θ)=-cos θ` so the two Compton shifts
    sum to twice the electron Compton wavelength. Insert its calibrated
    picometre value and prove the D rounding/uniqueness predicates by cases.

39. **`PhyXMiniProblems/problem_phyx_mini_0531.lean`.**
    Resolve momentum conservation along and transverse to the equal-angle
    geometry, combine it with photon and electron dispersion, and eliminate
    the scattered photon variables to obtain the stated rational SI momentum.
    Bound that expression against all four displayed values to prove D is
    closest.

40. **`PhyXMiniProblems/problem_phyx_mini_0532.lean`.**
    Derive the electron momentum/wavelength from `54 eV`, use the first-maximum
    Bragg relation and figure angle to isolate the column spacing, and prove
    the `0.2175–0.2185 nm` interval with certified sine and square-root bounds.
    Enumerate the displayed spacings for unique closest D.

41. **`PhyXMiniProblems/problem_phyx_mini_0533.lean`.**
    Evaluate the semiclassical attenuation and exact finite-barrier formulas
    independently from the same positive opacity. Prove the approximation is
    nearest D near `0.01023`, the exact coefficient lies within `1e-4` of
    `0.0401`, and finite case analysis shows no displayed choice matches the
    exact coefficient.

42. **`PhyXMiniProblems/problem_phyx_mini_0534.lean`.**
    Divide the two positive dispersion equations and select the positive root
    to obtain `k₂/k₁=sqrt (2/7)`. Substitute into the flux coefficient, prove
    a tight radical interval around `0.9079866`, and discharge the D rounding
    and nearest-choice claims.

43. **`PhyXMiniProblems/problem_phyx_mini_0535.lean`.**
    Expand and group the kinetic and six Coulomb terms to the stated
    `A/d²-B/d` curve. Complete the square after substituting `x=1/d>0` (or
    compare factored differences) to prove the unique minimizer
    `2π²ℏ²/(21kme²)`, then certify its picometre interval and D closestness.

44. **`PhyXMiniProblems/problem_phyx_mini_0536.lean`.**
    Compute each depicted Balmer energy gap by cases and prove `3→2` is the
    unique smallest. Solve the positive photon product for wavelength and
    reverse the strict gap ordering to show it is uniquely longest; keep any
    unsupported displayed whole-nanometre metadata separate from this physical
    conclusion.

45. **`PhyXMiniProblems/problem_phyx_mini_0537.lean`.**
    Rearrange the green transition energy law to
    `E₂=E₄*-hc/λ`, then convert the calibrated readouts coherently to eV.
    Bound the result within `0.02 eV` of `18.37` and enumerate choices to prove
    unique D.

46. **`PhyXMiniProblems/problem_phyx_mini_0538.lean`.**
    Prove the carbon radius from regular-hexagon geometry and the hydrogen
    radius by radial bond addition. Reindex the finite point-mass sum into six
    equal terms of each species, evaluate the calibrated SI rational, and
    prove it rounds uniquely to D.

47. **`PhyXMiniProblems/problem_phyx_mini_0539.lean`.**
    For each dynode, rewrite the `100 V` gap and ideal efficiency into yield
    `10`; propagate the natural counts through the six recurrence steps to
    `10^6`. Multiply the final `100 eV` impact energy to obtain `10^8 eV` and
    reduce the D equality.

48. **`PhyXMiniProblems/problem_phyx_mini_0540.lean`.**
    Rearrange vector momentum conservation, square the norm, and use the
    supplied included angle to derive the cosine-rule relation. Convert the
    curvature momentum readouts to MeV/c, certify the resulting scalar
    interval, and compare its absolute error with all four choices to select
    D.

49. **`PhyXMiniProblems/problem_phyx_mini_0541.lean`.**
    Close both sphere-membership obligations by expanding the three
    coordinates and applying `sin_sq_add_cos_sq`. Then apply the spin-half
    transition law with the first-axis spherical direction and the x-axis,
    simplify the dot product, and derive the requested outcome probability
    and displayed result without using the unrelated raster as physics.

50. **`PhyXMiniProblems/problem_phyx_mini_0542.lean`.**
    Rewrite the two sequential filter probabilities from the Born rule as
    `cos²(θ/2)` and `sin²(θ/2)`. Multiply them and use
    `sin θ = 2 sin(θ/2) cos(θ/2)` to obtain
    `(1/4)sin² θ`; unfold `IsCorrectAnswer` to close choice D.

51. **`PhyXMiniProblems/problem_phyx_mini_0543.lean`.**
    Expand the x-spin eigenstates in the z basis, apply diagonal Zeeman
    evolution, and simplify the inner product to `i sin(ωt/2)`. The Born rule
    plus `Complex.normSq (i·r)=r²` gives the probability for every nonnegative
    time; reduce the D display definition.

52. **`PhyXMiniProblems/problem_phyx_mini_0544.lean`.**
    Solve continuity and derivative matching for reflection/transmission
    amplitudes, use the positive dispersion roots
    `k₁∝sqrt E`, `k₂∝sqrt(E-V)`, and simplify the flux coefficient to the
    displayed D expression. Reuse the helper for both equality conjuncts and
    reduce the metadata equality.

53. **`PhyXMiniProblems/problem_phyx_mini_0545.lean`.**
    Use reflection symmetry of each normalized square-well eigenstate (or
    integrate `sin²`) to prove right-half probability `1/2` for all positive
    levels. Substitute this in first-order perturbation theory, normalize the
    NNReal scalar action, and prove the unique displayed fraction D by cases.

54. **`PhyXMiniProblems/problem_phyx_mini_0546.lean`.**
    Prove the rectangle area from its height/width readouts; establish the
    approximate-identity limit by restricting to the shrinking centered
    interval and continuity at `L/2`. Evaluate the ground density there as
    `2/L`, substitute in the Dirac expectation to get `2V₀`, and finish the
    answer predicate.

55. **`PhyXMiniProblems/problem_phyx_mini_0548.lean`.**
    Eliminate electron momentum and final energy from four-momentum
    conservation, use `Eγ=pc` and the electron mass shell, and factor the
    resulting Compton relation. Clear only positive denominators to isolate
    `ν'` in the stated formula.

56. **`PhyXMiniProblems/problem_phyx_mini_0549.lean`.**
    Subtract the photoelectric equations at graph points A and B to cancel the
    work function, rewrite the calibrated rise/run, and obtain
    `h=e·2/(5·10^14)`. Bound the calibrated value inside D's `5e-36` tolerance
    and outside the other three intervals.

57. **`PhyXMiniProblems/problem_phyx_mini_0550.lean`.**
    Rewrite the normalized quadratic wave profile and Born integrals on the
    box interval. Evaluate the polynomial antiderivatives, use normalization
    to cancel the amplitude scale, and simplify the origin-to-one-third ratio
    to `17/81`.

58. **`PhyXMiniProblems/problem_phyx_mini_0551.lean`.**
    Solve one-dimensional momentum conservation for the signed thorium recoil,
    using its positive nonzero mass. Substitute into both kinetic-energy laws
    and the total-energy sum; evaluate the mass/speed readouts and compare the
    exact result against the four displayed energies to prove D uniquely
    closest.

59. **`PhyXMiniProblems/problem_phyx_mini_0552.lean`.**
    Use the simultaneous platform length and contraction law to recover the
    rocket proper length `γ·65`; divide by the positive rocket-frame traversal
    speed `0.8c`. Reduce `γ(0.8)=5/3` and bound the exact Physlib-calibrated
    microsecond result within `0.005` of D.

60. **`PhyXMiniProblems/problem_phyx_mini_0553.lean`.**
    Substitute `4/5` and `3/5` in Einstein velocity addition and normalize to
    `35/37`. Unfold rounding and unique matching, split on answer choices, and
    close the rational absolute inequalities with `norm_num`.

61. **`PhyXMiniProblems/problem_phyx_mini_0554.lean`.**
    Rewrite total energies as rest plus kinetic energy in the reaction energy
    conservation law, cancel the stationary target terms, and insert all MeV
    rest/kinetic readouts. `ring_nf`/`norm_num` yields `78.9 MeV`; the second
    conjunct follows by unfolding recorded choice D.

62. **`PhyXMiniProblems/problem_phyx_mini_0555.lean`.**
    Evaluate the initial invariant `s` for a beam on a stationary proton and
    set it equal to the four-particle threshold invariant. Use positive-energy
    branches to derive beam total energy `7m_p` and kinetic energy `6m_p`;
    insert `0.938 GeV`, then prove D and uniqueness by finite cases.

63. **`PhyXMiniProblems/problem_phyx_mini_0556.lean`.**
    Resolve momentum conservation into x/y components and divide by the
    positive x component to establish the tangent helper. Substitute the
    relativistic momenta from the readouts, use the acute angle branch, and
    certify the arctangent degree interval `[12.65,12.75)`; enumerate choices
    for unique D.

64. **`PhyXMiniProblems/problem_phyx_mini_0557.lean`.**
    Derive the wavelength interval from `λ=h/sqrt(2mE)` by squaring positive
    bounds. Use Bragg's law and `sin θ≤1` to exclude every natural order above
    one; then bound the acute `arcsin(λ/(2d))` angle in
    `[34.35°,34.45°)` and reduce the rounding/uniqueness claims.

65. **`PhyXMiniProblems/problem_phyx_mini_0558.lean`.**
    Evaluate the two reciprocal Einstein transforms at `3/5` and `-4/5` to
    obtain `±35/37`. Simplify absolute values using signs, unfold the
    hundredth-rounding predicates, and eliminate choices to prove unique D.

66. **`PhyXMiniProblems/problem_phyx_mini_0559.lean`.**
    Compute rest volume `2·2·4=16`, apply volume contraction
    `V'=V/γ(13/20)`, and algebraically reduce the result to
    `(4/5)sqrt 231`. Prove the one-decimal D interval and nearestness by
    squaring rational bounds for `sqrt 231`.

67. **`PhyXMiniProblems/problem_phyx_mini_0560.lean`.**
    Read the observer condition from the boosted spatial x component and solve
    for the boost parameter. Substitute it into the Lorentz temporal component
    to obtain `E'=E sqrt(1-u_x²)`; rewrite
    `u_x=-u sin α`, simplify squares, and unfold displayed choice D.

68. **`PhyXMiniProblems/problem_phyx_mini_0561.lean`.**
    Eliminate the selector speed, plate transit time, and drift time to derive
    the exact correction formula. Evaluate the neglect calculation and then
    the accepted-calibration formula to the stated rational microtesla value;
    use exact rational absolute comparisons to prove the requested displayed
    choice/closestness.

69. **`PhyXMiniProblems/problem_phyx_mini_0562.lean`.**
    Derive `θ=π-2β`, then rewrite the contact triangle with
    `sin β=cos(θ/2)` to obtain `b=R cos(θ/2)`. Substitute into the cross-section
    and rate laws, carrying the explicit normalization factor; prove both the
    full-disk and source-convention conclusions separately and select D only
    under the premise that fixes the source normalization.

70. **`PhyXMiniProblems/problem_phyx_mini_0563.lean`.**
    Combine `I=(2/5)MR²` with `L=Iω`, and derive the ring magnetic moment
    `QωR²/2`. Substitute both in the gyromagnetic law, cancel positive
    `Q,M,R,ω`, and solve `g=5/2`; cases on choices prove D is unique.

71. **`PhyXMiniProblems/problem_phyx_mini_0564.lean`.**
    From uniform rotation and straight flight prove offset
    `f·distance/meanSpeed`. Rewrite Maxwell's mean-speed law and all unit
    conversions, then certify the square-root quotient within `1e-5` of
    `0.05021`; compare exact rational intervals to prove D uniquely nearest.

72. **`PhyXMiniProblems/problem_phyx_mini_0565.lean`.**
    Expand the planar Lorentz boost into longitudinal and transverse velocity
    components, substitute the polar readouts, and simplify their Euclidean
    norm to `expectedRocketSpeedFractionInOPrime`. Bound that expression in
    the `0.69±0.005` interval and enumerate choices for unique B.

73. **`PhyXMiniProblems/problem_phyx_mini_0566.lean`.**
    Expand both triangle areas as determinant absolute values relative to C;
    replace longitudinal coordinate differences by division by `γ` and
    transverse differences unchanged. Factor the positive `1/γ` from the
    determinant, then insert area `3` and `γ(3/5)=5/4` to get `12/5`; keep the
    inconsistent source choices as metadata rather than proving B.

74. **`PhyXMiniProblems/problem_phyx_mini_0567.lean`.**
    Rewrite the wavelength ratio as `49/50`, square the approaching-source
    Doppler law, and solve the subluminal nonnegative branch for `β=99/4901`.
    Scale by `c`, then use rational absolute comparisons to show printed B is
    uniquely closest despite not being the exact two-percent wavelength value.

75. **`PhyXMiniProblems/problem_phyx_mini_0568.lean`.**
    Use midpoint geometry and invariant light speed to show each flash takes
    `(L₀/2)/c`; rewrite `L₀/2=120 m`. Bound
    `120/299.792458` within `0.005 μs` of `0.4`, then enumerate choices to
    establish both flashes uniquely match B.

76. **`PhyXMiniProblems/problem_phyx_mini_0569.lean`.**
    Eliminate the backscattered photon and electron momentum/energy using
    conservation and the mass shell to derive the general rational recoil
    fraction. Insert `E=100 keV`, `M=511 keV` to obtain
    `122200/383321`, prove its `0.32` interval, direction, and unique C
    closestness.

77. **`PhyXMiniProblems/problem_phyx_mini_0570.lean`.**
    Equate `exp(-2κd)=exp(-1)`, use injectivity of `exp`, and solve
    `d=1/(2κ)`; substitute the positive decay root for the closed form. Square
    calibrated rational bounds to place the nanometre readout in C's
    three-decimal interval and prove unique nearestness.

78. **`PhyXMiniProblems/problem_phyx_mini_0571.lean`.**
    Derive the two hydrogen distances from bisector geometry and sum their
    point-mass inertia. Combine the rigid-rotor `0→1` gap with
    `Eλ=2πℏc`, then certify the result within `1 μm` of `344` and strictly
    nearer C than all alternatives.

79. **`PhyXMiniProblems/problem_phyx_mini_0573.lean`.**
    Rewrite event count, mass defect, and energy-per-event laws to the displayed
    exact expression, cancel the common atomic-mass-unit factor only after
    establishing nonzero conversion constants, and normalize the remaining
    rational calculation. Prove the two-decimal tolerance for `8.65` and
    reduce recorded C.

80. **`PhyXMiniProblems/problem_phyx_mini_0574.lean`.**
    Specialize the five step laws, unfold alpha/beta-minus updates, and use
    `omega` on the natural mass/proton-number equalities to derive `(225,89)`.
    Apply isotope extensionality and unfold choice C to prove the endpoint
    isotope equality.

81. **`PhyXMiniProblems/problem_phyx_mini_0575.lean`.**
    Subtract the two conduction-band depth readouts to obtain donor-minus-Fermi
    energy `-0.04 eV`, then rewrite the Fermi–Dirac law. Certify the
    exponential at `300 K` tightly enough for the one-thousandth agreement
    and compare intervals to prove C uniquely nearest.

82. **`PhyXMiniProblems/problem_phyx_mini_0576.lean`.**
    Derive `λ=log 2/2` from the two-second half-life using positivity and
    exponential/log identities, then substitute the population and activity
    laws at `27 s`. Rewrite the exponential using powers of two where possible
    and prove the exact expression lies within `0.5 Bq` of `60`.

83. **`PhyXMiniProblems/problem_phyx_mini_0577.lean`.**
    Subtract the two stimulated-emission/level equations to express `E₂-E₁`
    from the calibrated frequency/wavelength data. Convert coherently to
    micro-eV, prove the `6.87±0.03` interval, and establish recorded C and
    unique closestness by choice cases.

84. **`PhyXMiniProblems/problem_phyx_mini_0578.lean`.**
    Subtract the two radiative-transition equations, use the common lower
    level and Zeeman splitting to get `|ΔEγ|=2μ_BB`; replace photon energies by
    `hc/λ` and solve for positive B. Bound the calibrated expression in
    `(18,18.5) T`, then unfold matching and enumerate choices for unique C.

85. **`PhyXMiniProblems/problem_phyx_mini_0579.lean`.**
    Normalize the level difference to `31/250 eV`, then combine
    Planck–Einstein and `c=λν`, clearing positive energy/frequency factors, for
    the exact SI wavelength. Bound its micrometre conversion within `0.05` of
    `10.0` and prove unique C by cases.

86. **`PhyXMiniProblems/problem_phyx_mini_0580.lean`.**
    Treat occupations as finite natural variables: use Pauli caps, total count
    `22`, strict level order, and minimality exchange arguments to force
    `(2,6,6,6,2,0)`. Substitute into additive energy, use zero interaction,
    and normalize the finite sum to multiplier `186`, matching C.

87. **`PhyXMiniProblems/problem_phyx_mini_0581.lean`.**
    Use caps, count, and minimality to prove ground occupation
    `(2,6,3,0,0)` and multiplier `65`; apply the least-strictly-higher
    characterization to force first excited occupation `(2,5,4,0,0)`.
    Evaluate its sum as `66` and unfold the C match.

88. **`PhyXMiniProblems/problem_phyx_mini_0582.lean`.**
    Sum the two point masses at radius `d/2` to get `I=md²/2`, eliminate
    angular speed between `L=Iω` and `E=Iω²/2`, and substitute
    `L_n=nh/(2π)`. Clear positive inertia/length denominators and `ring` to the
    stated `n²h²/(4π²md²)` target and corresponding displayed choice.

89. **`PhyXMiniProblems/problem_phyx_mini_0583.lean`.**
    Rewrite the square-corral eigenstate and rectangular probe region in
    Born's integral, separate the product integral, and evaluate the two
    trigonometric antiderivatives/bounds. Prove the result belongs to the
    `0.0014±0.00005` interval; the main C match then unfolds directly.

90. **`PhyXMiniProblems/problem_phyx_mini_0584.lean`.**
    Convert peak counts to `n_x=5,n_y=3`, and peak spacings to
    `L_x=15 nm,L_y=6 nm`. Substitute these into the rectangular-well spectrum,
    simplify `n_x/L_x` and `n_y/L_y`, and derive the exact SI expression plus
    the stated electron-volt interval; do not equate it with the malformed
    symbolic metadata.

91. **`PhyXMiniProblems/problem_phyx_mini_0585.lean`.**
    Rewrite entry kinetic plus potential energy to `11 eV`; subtract each
    bound-level readout to compute the three capture photon energies. Show E3
    gives `7 eV` and is no larger than the other two by finite cases, construct
    the least-energy witness, and reduce the displayed choice C.

92. **`PhyXMiniProblems/problem_phyx_mini_0586.lean`.**
    Use the continuum cutoff photon to solve for E1, then the line photon to
    solve for E2, preserving the exact wavelength-constant expression.
    Establish a certified interval within `0.5 eV` of `109` and outside every
    other displayed interval to prove unique C.

93. **`PhyXMiniProblems/problem_phyx_mini_0587.lean`.**
    Identify the longest listed transition as `n=2→3`, combine its energy gap
    with `hc/λ`, and clear positive factors to derive the exact `L²` relation.
    Select the positive square-root branch and certify `349.5<L_pm<350.5`,
    then prove C uniquely nearest.

94. **`PhyXMiniProblems/problem_phyx_mini_0588.lean`.**
    Rewrite photon energy from the source figure, convert incident power to a
    photon rate, and apply the detector absorption/efficiency laws to obtain a
    tight interval around `6.0 s⁻¹`. Unfold the matching predicates and
    enumerate choices to prove C is the only value within `0.05`.

95. **`PhyXMiniProblems/problem_phyx_mini_0589.lean`.**
    Translate the two pilot approach magnitudes to signed Einstein transforms,
    clear their positive denominators, and solve the resulting polynomial for
    βB. Use `|βB|<1` and direction hypotheses to exclude the superluminal root,
    obtaining `1/2`; choice uniqueness is finite `norm_num`.

96. **`PhyXMiniProblems/problem_phyx_mini_0590.lean`.**
    Substitute the two given Earth velocities in the equal-approach equation,
    clear positive subluminal denominators, and solve the quadratic. Use
    `sqrt 19>0` and the physical interval to select
    `(86-3sqrt 19)/85`; square rational bounds for `sqrt 19` to prove the
    `0.858` interval and unique C.

97. **`PhyXMiniProblems/problem_phyx_mini_0591.lean`.**
    Normalize the Lorentz velocity transform with the two signed Earth-frame
    readouts to get `-35/37`. Apply the magnitude law and negativity to obtain
    approach speed `35/37`, then unfold rounding/uniqueness and close choice C
    by rational arithmetic.

98. **`PhyXMiniProblems/problem_phyx_mini_0592.lean`.**
    Read intercept `γΔx'=2` and slope `γv=0.7`, use
    `γ²(1-v²/c²)=1`, and eliminate `v,γ` to derive the positive square-root
    expression. Bound it with the exact Physlib `c` readout inside C's display
    interval and compare it with all alternatives.

99. **`PhyXMiniProblems/problem_phyx_mini_0593.lean`.**
    Subtract the two pulse worldline equations to obtain
    `τ_R=τ(c+v)/c`. Combine with `τ=γτ₀`, rewrite γ, and prove the positive
    radical identity
    `γ(c+v)/c=sqrt((c+v)/(c-v))`; positivity and `0<v<c` also yield both strict
    interval inequalities.

100. **`PhyXMiniProblems/problem_phyx_mini_0594.lean`.**
    Solve the two emission-to-arrival light paths to obtain
    `v_app/c=β sin θ/(1-β cos θ)`. Rewrite `β=0.98`, `θ=30°`, use exact
    half-angle trig values, and certify the result within `0.005` of `3.24`,
    closing C.

101. **`PhyXMiniProblems/problem_phyx_mini_0595.lean`.**
    On the punctured left neighborhood of `1`, rewrite the function with the
    Einstein formula. Prove the denominator tends to `1-u` and is nonzero
    because the fixed particle speed is subluminal, then use limit arithmetic
    to simplify `(u-1)/(1-u)` to `-1`, choice C.

102. **`PhyXMiniProblems/problem_phyx_mini_0597.lean`.**
    Specialize the Lorentz law at frame speed zero and the graph ordinate to
    derive laboratory velocity `0.8c`. Rewrite the moving-frame longitudinal
    velocity as `c(0.8-v/c)/(1-0.8v/c)` for `v<c`; apply quotient limit rules
    at `v→c⁻`, using `c>0`, to obtain `-c`.

103. **`PhyXMiniProblems/problem_phyx_mini_0598.lean`.**
    Substitute the graph spacetime separations and boost readout in the Lorentz
    time transformation, simplify to an exact radical/rational expression,
    and prove it lies in C's `5e-9 s` tolerance. Enumerate choices and show
    their intervals are disjoint for uniqueness.

104. **`PhyXMiniProblems/problem_phyx_mini_0599.lean`.**
    Use the zero-speed point and vertical-axis calibration to derive proper
    time `8 s`, then specialize time dilation at `49/50`. Reduce γ to
    `50/sqrt 99`, prove the resulting duration lies within `0.5 s` of `40`,
    and compare it strictly with the other displayed times.

105. **`PhyXMiniProblems/problem_phyx_mini_0600.lean`.**
    Divide the positive inside/outside dispersion equations to get squared
    wave-number ratio `4`, then select ratio `2`. Substitute into the
    transmitted flux coefficient for `8/9`, prove the `0.8889` rounding and
    nearest C claims; invoke the separate capture premise only for any
    absorption-equals-entry conclusion.

106. **`PhyXMiniProblems/problem_phyx_mini_0601.lean`.**
    Solve the delta continuity/jump linear system for left and right incident
    amplitudes to build the symmetric scattering matrix. Use the declared
    transfer convention, determinant-one law, and left-incidence boundary
    values to derive `T=1/normSq(M₁₁)`; assemble the target and unfold choice C.

107. **`PhyXMiniProblems/problem_phyx_mini_0602.lean`.**
    Specialize the local delta transfer law at `±a/2`, rewrite the ordered
    composition law, and compute the `2×2` matrix product entrywise to the
    explicit matrix. Substitute its `M₁₁` into the left-incidence observable
    law and simplify complex norm squares to the physically supported
    transmission coefficient.

108. **`PhyXMiniProblems/problem_phyx_mini_0603.lean`.**
    Rewrite the spinless ground-state law as the sum of the first N
    one-particle levels, factor out the common energy scale, and use the
    finite sum-of-squares formula. Divide by atom count only after using its
    positivity, simplify to `((N+1)(2N+1))/(6N)`, and unfold choice C.

109. **`PhyXMiniProblems/problem_phyx_mini_0604.lean`.**
    Prove the six-direction cardinality by product/cardinality reduction.
    Rewrite the quantized oscillator partition function as a geometric series,
    differentiate/log-differentiate to obtain the Einstein heat-capacity
    factor, multiply by `3N`, and establish the requested low/high-temperature
    limits and figure-unit conversion with standard exponential limits.

110. **`PhyXMiniProblems/problem_phyx_mini_0605.lean`.**
    Normalize the three trough readouts to adjacent spacing `4 cm⁻¹`, then use
    the spectrometer calibration to obtain the frequency separation. Derive
    `I=μa²` from center-of-mass distances, equate the rotor line-spacing law,
    isolate positive bond length by square root, and certify the displayed
    rounding/unique choice.

111. **`PhyXMiniProblems/problem_phyx_mini_0606.lean`.**
    Decompose three spin-1/2 tensor factors into total-spin `S=1/2` and
    `S=3/2` sectors and rewrite
    `Σ S_i·S_j=(S_tot²-3·3ℏ²/4)/2`. Positive antiferromagnetic coupling makes
    the two `S=1/2` doublets the four-dimensional ground eigenspace with energy
    `-3Jℏ²/4`; reduce choice C.

112. **`PhyXMiniProblems/problem_phyx_mini_0607.lean`.**
    Normalize Einstein addition to derive missile speed `55/64 c`, then use
    the positive intercept equation for the exact flight-time quotient.
    Bound the Physlib light-speed-calibrated value against all four displayed
    times to prove A is uniquely closest, without replacing the exact time by
    `31.0 s`.

113. **`PhyXMiniProblems/problem_phyx_mini_0608.lean`.**
    From equal apparent axes derive `γ=7/5`; square the positive Lorentz-factor
    equation and select the nonnegative speed branch
    `β=sqrt(24/49)`. Multiply by exact `c` and prove the result is within
    `500000 m/s` of choice A using rational square bounds.

114. **`PhyXMiniProblems/problem_phyx_mini_0609.lean`.**
    Project the general Lorentz magnetic-field transformation onto the
    subspace perpendicular to the boost. Rewrite the zero electric field term
    to zero, distribute the projection over scalar multiplication, and
    simplify to `B'⊥=γ • B⊥`.

115. **`PhyXMiniProblems/problem_phyx_mini_0610.lean`.**
    Rewrite the yellow region as the axis-aligned rectangle specified by the
    worldsheet/event data. Apply the rectangle area law, replace the vertical
    `ct` side by `c·T` in arbitrary compatible units, and use commutative-ring
    normalization to get `cLT`.

116. **`PhyXMiniProblems/problem_phyx_mini_0612.lean`.**
    Use minimality plus continuity/monotonicity of the switch-a divider to show
    stopping occurs at equality, then substitute the previous work function,
    `65 nm` photon energy, and circuit laws. Solve the positive rational
    resistance equation, certify `|R_kΩ-13.8|<0.05`, and use interval
    disjointness for unique A.

117. **`PhyXMiniProblems/problem_phyx_mini_0613.lean`.**
    Rearrange total energy conservation for the helper. For the main target,
    combine photon `E=pc` with `p=h/λ` for the first exact expression; expand
    the massive total energies, stationary-target condition, and equal
    electron/positron data for the second. Keep the unsupported numerical
    answer A as metadata.

118. **`PhyXMiniProblems/problem_phyx_mini_0614.lean`.**
    Differentiate the Planck spectral-exitance formula at the positive maximum,
    clear positive denominators, and derive
    `3(1-exp(-x₀))=x₀`. Combine the narrow-band power law, area, ideal
    conversion, `P=VI`, and Ohm's law to get `I²R`; then use certified bounds
    for the Wien root/exponential to prove the current interval and nearest A.

119. **`PhyXMiniProblems/problem_phyx_mini_0615.lean`.**
    Subtract the energy readouts to obtain incident `20 MeV`, solve the
    positive attenuation wave number from the dispersion law, and substitute
    it into the exact finite-barrier coefficient. Bound `sinh`/exponential
    terms tightly enough for the `0.014±0.0005` interval, then enumerate
    choices for unique A.

120. **`PhyXMiniProblems/problem_phyx_mini_0616.lean`.**
    Normalize the two energy readouts to the `7 eV` deficit, derive positive κ
    from the barrier decay law, and substitute it into the explicitly named
    leading opaque estimate. Prove the estimate lies between
    `1.6e-12` and `1.8e-12` with certified square-root/exponential bounds; do
    not identify the malformed energy-valued choice A with a probability.

121. **`PhyXMiniProblems/problem_phyx_mini_0617.lean`.**
    Define positive κ from the positive energy gap and solve the exterior
    constant-coefficient Schrödinger ODE as
    `C exp(κx)+D exp(-κx)`. Show any nonzero C contradicts the finite
    boundary/Tendsto condition, set `C=0`, and use exponential decay for the
    final limit.

122. **`PhyXMiniProblems/problem_phyx_mini_0618.lean`.**
    Rewrite the three atomic masses and normalize their difference to
    `5812/10^6 u`. Apply the mass-energy law and the eV/MeV conversions to the
    exact SI expression, then certify it is within `0.05 MeV` of `5.4` and
    reduce recorded C.

123. **`PhyXMiniProblems/problem_phyx_mini_0619.lean`.**
    Chain source activity, exposure geometry, photon energy/count, deposited
    energy, absorbed dose, and gamma weighting laws in coherent SI units.
    Normalize to millisieverts, prove the result lies within `0.005` of
    `0.45`, and compare rational distances to A, B, and D for unique C.

124. **`PhyXMiniProblems/problem_phyx_mini_0620.lean`.**
    Rewrite `n=3` in the orbital admissibility iff and use `omega` to reduce
    `ℓ<3` to `ℓ=0∨1∨2`. Specialize the spectrum with ground energy `-13.6 eV`
    to obtain `-68/45`; compare its exact distance to the four rational
    displays to prove the requested unique closest choice.

125. **`PhyXMiniProblems/problem_phyx_mini_0621.lean`.**
    Substitute the two `3/5 c` readouts into Einstein addition and clear the
    positive denominator to get `15/17`. Unfold the hundredth-rounding and
    uniqueness predicates, enumerate choices, and close the exact rational
    inequalities for C.

126. **`PhyXMiniProblems/problem_phyx_mini_0622.lean`.**
    Specialize the axis-sensitive length law: transverse height remains `1`,
    while longitudinal width is `(3/2)/γ(9/10)`. Reduce γ to
    `10/sqrt 19`, prove the width lies in `(0.645,0.655)`, and close the
    displayed C predicate.

127. **`PhyXMiniProblems/problem_phyx_mini_0623.lean`.**
    Combine relativistic energy–momentum with de Broglie to derive the exact
    wavelength including the `(K/c)²` correction. Use first-order diffraction
    to obtain `d=λ/sin 24°`, then certify square-root and sine bounds yielding
    `0.295≤d_nm<0.305`; unfold matching and enumerate choices for unique C.

128. **`PhyXMiniProblems/problem_phyx_mini_0624.lean`.**
    Evaluate both reciprocal Einstein transforms from the signed Earth-frame
    fractions to obtain `-15/23` and `15/23`. Simplify their absolute values
    using signs, prove both lie in the `0.65±0.005` interval, and eliminate the
    other displayed choices to establish unique recorded C.
