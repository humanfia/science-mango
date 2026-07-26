# Iteration 015 Plan

## Batch contract

- Preserve exactly the 128 loop-selected Current Objectives below, in their
  existing order: 16 mandatory proof-Review retries followed by 112 new
  accepted-open targets. No `proof_review_exhausted` target is present.
- Eligibility shortfall: 0. The fixed objective list exceeds the requested
  `max_parallel = 32` occupancy by 96 targets; Plan does not mutate or
  silently truncate that list. Execution must keep the first 16 retry lanes
  ahead of the new lanes while respecting its actual concurrency limit.
- Preserve every theorem signature and physical hypothesis. Obtain numerical
  choices only from the stated readouts and governing laws; certify `pi`,
  radical, trigonometric, and inverse-trigonometric rounding bounds rather
  than assuming decimals.
- The supplied blueprint excerpts expose no concrete chapter-level proof
  strategy defect, so no blueprint chapter is changed. Targets `0110`,
  `0118`, `0120`, and the helper in `0169` have explicit hypothesis/source
  insufficiencies; keep any unavoidable remainder honest rather than adding
  unsupported data or weakening a statement.

## Per-target proof strategy

1. **`PhyXMiniProblems/problem_phyx_mini_0071.lean` (retry; 2/3 used).**
   Retain the Snell-law derivation `sin θ = 100/133`, prove cosine positivity
   from the acute branch, and obtain the two tangent bounds by multiplying
   through only positive denominators. Rewrite the width law to trap the depth
   in `[55,65]`, then unfold the nearest-mark predicate and finish by linear
   arithmetic; avoid an unqualified nonlinear cancellation step.

2. **`PhyXMiniProblems/problem_phyx_mini_0075.lean` (retry; 2/3 used).**
   Rewrite the Rayleigh and exact screen-geometry laws at millimeter units,
   preserve the exact `centralAngleDiameterRatio` equality, and transport the
   supplied cubic angular remainder through multiplication by the positive
   chart distance. Normalize the final product with `abs_mul` and `ring`,
   keeping the paraxial conclusion an error bound rather than an equality.

3. **`PhyXMiniProblems/problem_phyx_mini_0082.lean` (retry; 2/3 used).**
   Reuse the exact first-two-fringe values and prove the display intervals
   from certified lower and upper bounds on `π²`; discharge every division
   with `π² > 0`. Rewrite the exact values into the target before unfolding
   the answer predicate so the proof never treats `5.7` or `2.9` as exact.

4. **`PhyXMiniProblems/problem_phyx_mini_0088.lean` (retry; 2/3 used).**
   Derive the first-minimum length from the graph, specialize the optical-path
   law at `750` and `1200`, and use the common index increment to scale the
   half-wavelength path to `4/5 λ`. For the phase equality, introduce the
   wavelength nonzero fact explicitly and use `div_eq_iff` plus `ring`
   instead of a terminal in-place `field_simp`.

5. **`PhyXMiniProblems/problem_phyx_mini_0089.lean` (retry; 2/3 used).**
   Work in one fixed unit system, derive the material length
   `L = 5λ/4`, and rewrite the optical-path and phase laws with equal baseline
   and reflection phases. Cancel `2π` and then the positive wavelength in
   separate equalities, yielding the exact phase-in-wavelengths result before
   unfolding the answer choice.

6. **`PhyXMiniProblems/problem_phyx_mini_0096.lean` (retry; 2/3 used).**
   Keep the critical-ray `IsGreatest` proof and isolate the display proof:
   certify the argument's interval, use the principal `arcsin` monotonicity
   lemmas on the physical branch, and prove the strict degree interval
   `71.95 < θ < 72`. Convert this interval to the stated source tolerance by
   `abs_le`; do not identify the prediction exactly with `72.1°`.

7. **`PhyXMiniProblems/problem_phyx_mini_0110.lean` (retry; 1/3 used).**
   First attempt to derive an attained upper bound for
   `attainableImageDiametersCm` from the frozen finite-ray and local Snell
   hypotheses, then prove its `24.1 cm` rounding and reuse uniqueness of an
   `IsGreatest` element. The excerpt shows no link from the local derivative
   to the finite-cap image family, so if no such consequence is present,
   leave the maximum-existence subgoal as the documented honest blocker; do
   not promote the recorded answer to a premise.

8. **`PhyXMiniProblems/problem_phyx_mini_0115.lean` (retry; 1/3 used).**
   Derive the two endpoint image coordinates from the thin-lens laws, expand
   the Euclidean distance, and simplify it to `3200√10/593`. Prove the needed
   lower and upper bounds on `√10` by squaring with `sqrt_nonneg` and
   `sq_sqrt`, then close the tenth-centimeter and closest-choice comparisons
   case by case.

9. **`PhyXMiniProblems/problem_phyx_mini_0116.lean` (retry; 1/3 used).**
   Rewrite the round-trip optical path and destructive half-cycle law in
   micrometers to show `79/720` is attainable at order zero. For arbitrary
   destructive depth, extract its natural-number order and use
   nonnegativity to prove the lower bound; finish the displayed-choice
   uniqueness with exact rational absolute-value comparisons.

10. **`PhyXMiniProblems/problem_phyx_mini_0118.lean` (retry; 1/3 used).**
    Preserve the proved symbolic axial-node formula and the meter-to-centimeter
    conversion. The supplied premises contain no numerical radius, frequency,
    sound speed, wavelength, or interference order, so the `11.3 cm`
    conclusion is underdetermined; leave that exact final specialization as
    the explicit blocker rather than inventing a readout.

11. **`PhyXMiniProblems/problem_phyx_mini_0120.lean` (retry; 1/3 used).**
    Complete the closest-positive-maximum argument only to the supported
    formula `y = R λ/d`, with all length denominators discharged from the
    physical hypotheses. Since no premise fixes the numerical value of
    `R λ/d`, keep the `13/4 mm` conjunct and dependent answer uniqueness as
    an honest source-redraft blocker.

12. **`PhyXMiniProblems/problem_phyx_mini_0127.lean` (retry; 1/3 used).**
    Use the constructive-reflection iff at thickness `100` with order zero
    and the stated `n,λ` readouts. For an arbitrary positive constructive
    thickness, extract the natural order and prove `100 ≤ t` by
    nonnegativity; apply this leastness to the actual positive green film.

13. **`PhyXMiniProblems/problem_phyx_mini_0150.lean` (retry; 1/3 used).**
    For each wavelength, convert the angle-valued Snell equations to real
    representatives only after proving every angle and sum lies in the
    principal interval. Derive prism geometry and the exit sine ratio, then
    close with `arcsin_sin` on the certified emergence branch and rewrite the
    two figure labels.

14. **`PhyXMiniProblems/problem_phyx_mini_0158.lean` (retry; 1/3 used).**
    Cancel the positive refracted slope and nonzero glass index in separate
    steps to obtain `s' = s n₂/n₁` from the two paraxial ray intersections
    and Snell slope law. Rewrite the figure's `s = 5/2`, medium labels, and
    observer label only at the final theorem.

15. **`PhyXMiniProblems/problem_phyx_mini_0160.lean` (retry; 1/3 used).**
    Specialize the mirror equation to centimeters, prove the image distance
    readout nonzero before clearing denominators, and solve `q = 35`.
    Substitute this and `p = 14` into the signed magnification law to obtain
    `-5/2`, then unfold the displayed-answer predicate.

16. **`PhyXMiniProblems/problem_phyx_mini_0169.lean` (retry; 1/3 used).**
    In the main theorem, combine the collinear path identities with the
    physical nonnegativity of the initial listener distance to remove both
    absolute values, derive path difference `d`, and use the odd
    half-wavelength criterion to get the first displacement `343/1450`.
    The standalone helper lacks that nonnegativity hypothesis; if it cannot
    be recovered from its frozen geometry premise, leave only that helper
    gap explicitly blocked and do not assume the missing sign.

17. **`PhyXMiniProblems/problem_phyx_mini_0222.lean`.** Specialize the two
    directional Doppler laws with the still-air, source, observer, and emitted
    frequency readouts to obtain `119364/331` and `119364/355`. Subtract
    them under `abs`, prove the sign, normalize to `2864736/117505`, and
    close the half-hertz comparison with `24`.

18. **`PhyXMiniProblems/problem_phyx_mini_0223.lean`.** Subtract the two
    odd-quarter-wave resonance equations so the common end correction
    cancels and obtain spacing `λ/2`; insert the two tube lengths to get
    `λ = 27/50 m`. Use `v=fλ` with `v=343` for `17150/27 Hz`, then prove
    the nearest-whole-hertz choice by rational arithmetic.

19. **`PhyXMiniProblems/problem_phyx_mini_0224.lean`.** Rewrite the
    open-open fundamental geometry to `λ=2L=34/5 m`, substitute this and
    `v=343` into the wave relation, and cancel the positive wavelength to
    get `1715/34 Hz`. Unfold the tolerance for choice D and use `norm_num`.

20. **`PhyXMiniProblems/problem_phyx_mini_0225.lean`.** Eliminate angular
    speed between rolling without slip and `T=2π/ω`, then insert
    `R=0.300`, `v=3.00` to get `π/5`. Certify a tight rational interval for
    `π` sufficient for `0.628 ± 0.0005`, and compare all four absolute
    differences for uniqueness.

21. **`PhyXMiniProblems/problem_phyx_mini_0226.lean`.** Rewrite the elastic
    energy law with `k=83.8` and `x=0.0546 m`, normalize the exact rational
    energy, and unfold both answer predicates. Exact rational bounds show it
    lies within `0.0005 J` of `0.125` and strictly farther from A–C.

22. **`PhyXMiniProblems/problem_phyx_mini_0227.lean`.** Expand the
    uniform-meterstick inertia and center-of-mass distance in the physical
    pendulum law, divide by the reference simple-pendulum period using
    positivity, and obtain ratio `√(13/12)`. Prove a rational interval for
    this radical that gives the `4.08%` rounding and all closest-choice
    inequalities.

23. **`PhyXMiniProblems/problem_phyx_mini_0228.lean`.** Evaluate the rim
    inertia from the mass and radius readouts as `1/2000000`, then square the
    torsional-period law and cancel its positive quantities to derive
    `κ=π²/31250`. Use certified `π²` bounds to place this within the
    `3.16×10⁻⁴` display tolerance.

24. **`PhyXMiniProblems/problem_phyx_mini_0229.lean`.** Combine rod and
    point-mass inertia with the gravitational torque coefficient to derive
    the exact linearized period formula. Substitute `L=2`, `g=9.8` and use
    rational `π`/square-root bounds to prove the `2.68 s` interval and the
    four closest-choice inequalities.

25. **`PhyXMiniProblems/problem_phyx_mini_0230.lean`.** Use the SHM
    acceleration law and attainment of `|x|=A` to construct the maximum
    acceleration, then rewrite `ω=2π/T` and the graph readouts to obtain
    `π²/2`. Bound `π²/2` within `0.005` of choice D and discharge the
    remaining choice comparisons.

26. **`PhyXMiniProblems/problem_phyx_mini_0231.lean`.** Expand the non-slip
    predicate with `F_req=m_Bω²A` and `F_max=μ_sm_Bg`; use positivity to
    show the maximum must attain equality and solve
    `A=μ_sg/(2πf)²`. Insert the readouts, convert meters to centimeters, and
    certify the `6.62±0.005 cm` interval with `π²` bounds.

27. **`PhyXMiniProblems/problem_phyx_mini_0232.lean`.** Use derivative
    uniqueness at equilibrium to identify the rotational stiffness
    `κ=kL²`, combine it with `I=mL²/3`, and cancel positive `L²` to get
    `ω²=60`. Select the nonnegative oscillator root as `√60` and prove
    `7.745≤√60≤7.755` by squaring.

28. **`PhyXMiniProblems/problem_phyx_mini_0233.lean`.** Derive the spring
    torque coefficient `kh²`, add the gravitational coefficient `MgL`, and
    substitute the bob inertia `ML²` into the generalized oscillator. Use
    `ω=2πf`, positivity, and square-root algebra to obtain the displayed
    symbolic formula and then unfold the matching choice.

29. **`PhyXMiniProblems/problem_phyx_mini_0234.lean`.** Prove
    `sin θ-θ=o(θ)` from the derivative of `sin-id` at zero. Combine buoyancy,
    weight, inertial mass, the linearized Newton law, and `T=2π/ω` to solve
    the small-amplitude density relation; retain the nonlinear motion only
    through the supplied limit and residual statements.

30. **`PhyXMiniProblems/problem_phyx_mini_0235.lean`.** Divide the solid-disk
    inertia by `R²` using radius positivity to obtain effective rotational
    mass `M/2`, then rewrite the Physlib oscillator at both radius stages.
    Their identical positive squared frequencies imply equal frequencies;
    insert the mass/stiffness readouts and certify the displayed rounding.

31. **`PhyXMiniProblems/problem_phyx_mini_0236.lean`.** Derive the
    contact-end speed from energy conservation using the positive square-root
    branch. Use the first-maximum predicate and sine bounds to identify the
    quarter-period time, substitute the free and oscillatory trajectories,
    and algebraically cancel `k` to obtain the stated separation formula
    before checking its displayed value.

32. **`PhyXMiniProblems/problem_phyx_mini_0237.lean`.** Evaluate the spring
    kinetic-energy integral of the squared linear velocity profile to get
    `½(m/3)v²`; compare it with the effective-mass law at a nonzero test
    velocity to infer `m_eff=m/3`. Rewrite the effective oscillator period
    with `M+m/3` and conclude exact agreement with choice D.

33. **`PhyXMiniProblems/problem_phyx_mini_0238.lean`.** Unfold choice D to
    show it is exactly the frozen-length linearized pendulum period. For each
    emptying time, apply the stored small-angle and center-of-mass-drift error
    bounds and combine them by the triangle inequality to obtain the stated
    sum bound.

34. **`PhyXMiniProblems/problem_phyx_mini_0239.lean`.** Subtract common
    emission time from P- and S-wave arrival equations to derive the
    `40/3` distance factor. Use the noncollinear three-station geometry for
    trilateration uniqueness, construct the supplied ambiguity witnesses for
    sets of cardinality below three, and assemble the minimum-cardinality
    predicate.

35. **`PhyXMiniProblems/problem_phyx_mini_0240.lean`.** Derive
    `ω=10π` and `k=π/2` from the frequency and speed laws. Rewrite transverse
    acceleration as `-Aω² sin phase`; use `|sin|≤1` for the upper bound and
    choose a phase-attaining state for equality, then bound `12π²` inside the
    choice-D interval.

36. **`PhyXMiniProblems/problem_phyx_mini_0241.lean`.** Square the wave-speed
    laws in both trials, replace tensions by the static weights, and divide
    by the common positive density to get speed ratio squared `2/3`.
    Choose positive roots and use the calibrated speed `24`; prove the
    `19.6±0.05` interval for `24√(2/3)` by squaring.

37. **`PhyXMiniProblems/problem_phyx_mini_0242.lean`.** Use Pythagoras and
    positivity to derive each vertical component ratio `√7/4`; substitute
    `T=μv²` and the two equal tension components into vertical equilibrium.
    Normalize the mass to `72√7/49` and square rational bounds on `√7` to
    prove the `3.89 kg` display interval.

38. **`PhyXMiniProblems/problem_phyx_mini_0243.lean`.** Substitute
    centripetal tension into the string wave speed, rewrite density as cord
    mass over length, and use travel-time plus angular kinematics; cancel the
    positive radius, length, and angular speed to obtain `√(m_cord/m_block)`.
    Square tight rational bounds for the radical to close the `0.0843`
    rounding.

39. **`PhyXMiniProblems/problem_phyx_mini_0244.lean`.** Chain rolling,
    circulation, and stable-shape equalities to identify wave speed with
    center-of-mass speed. Substitute that result into `T=μc²` in every unit
    system and unfold the answer metadata to select quadratic scaling D.

40. **`PhyXMiniProblems/problem_phyx_mini_0245.lean`.** Convert the cavity
    resonance and rounded readouts into the finite mode-number disjunction
    near `980650`; eliminate inconsistent modes with exact interval
    arithmetic. Construct the next longer resonance using the adjacent lower
    mode number, prove its leastness among longer standing wavelengths, and
    bound its nanometer readout in A's unique rounding bin.

41. **`PhyXMiniProblems/problem_phyx_mini_0246.lean`.** Use Pythagoras to
    derive path lengths `10` and `√136`, then rewrite the phase and coherent
    intensity laws to obtain the exact ratio
    `2(1+cos(2π(√136-10)))`. Certify `√136`, reduce the phase to a controlled
    interval, bound cosine by a rational Taylor estimate, and finish the
    nearest-hundredth unique answer.

42. **`PhyXMiniProblems/problem_phyx_mini_0247.lean`.** Apply the controlled
    far-field error to trap the path difference near `1 m`; the out-of-phase
    first-maximum criterion then traps the wavelength near `2 m`. Transport
    these positive intervals through `f=c/λ`, use the vacuum speed readout,
    and prove only choice A lies within the half-megahertz window.

43. **`PhyXMiniProblems/problem_phyx_mini_0248.lean`.** Solve the exact
    two-point-source path-difference equation on the positive screen branch
    to get the stated `finiteScreenSymmetricSeparation` radical. Prove a
    rational interval for that radical which makes `round (10y)=158`, then
    unfold the finite answer table for uniqueness.

44. **`PhyXMiniProblems/problem_phyx_mini_0249.lean`.** Rewrite the leading
    estimator with the source readouts to obtain `211/2000 mm` and prove its
    unique `0.11 mm` display rounding. For the final limit, compose the exact
    ray-geometry scaling with the supplied Fraunhofer/paraxial asymptotics and
    close using `Tendsto` algebra, without equating the finite slit width to
    its estimate.

45. **`PhyXMiniProblems/problem_phyx_mini_0250.lean`.** Combine the
    double-pass optical-path increase `2L(n-1)` with the complete fringe
    count `Nλ`; cancel the positive cell length and substitute the readouts
    to solve the exact rational index. Exhibit the integer
    hundred-thousandth witness for `1.00034` and close the half-unit
    inequality by `norm_num`.

46. **`PhyXMiniProblems/problem_phyx_mini_0251.lean`.** At `t=0`, divide the
    displacement readout by the positive amplitude to get `cos φ=-1/3`;
    use the negative graph slope in the velocity law to prove `sin φ>0` and
    place `φ` in quadrant II. Apply injectivity of cosine there, then certify
    the `arccos(-1/3)` rounding with monotonic cosine bounds.

47. **`PhyXMiniProblems/problem_phyx_mini_0252.lean`.** Square the
    cyclic-to-angular relations and rewrite each oscillator stiffness to show
    `f_both²=30²+45²`. Use frequency positivity to select the square root,
    normalize it to `15√13`, and prove the half-hertz choice-C interval by
    squaring rational bounds on `√13`.

48. **`PhyXMiniProblems/problem_phyx_mini_0253.lean`.** Use
    `v(0)/v_m=4/5` and the graph branch sign to identify the fourth-quadrant
    representative `2π-arcsin(4/5)`. Prove positivity from the principal
    arcsine range and certify its `5.36±0.005` interval with rational bounds
    for `π` and `arcsin`.

49. **`PhyXMiniProblems/problem_phyx_mini_0254.lean`.** Divide the initial
    velocity equation by the nonzero position equation to obtain
    `tan φ=5/3`, and use the position/velocity signs plus the one-turn phase
    convention to select `arctan(5/3)`. Bound arctangent through monotonic
    tangent estimates and discharge the nearest-choice comparisons.

50. **`PhyXMiniProblems/problem_phyx_mini_0255.lean`.** Derive the struck
    block's mass from the spring period, apply elastic-collision momentum to
    the post-collision velocity, and use free-fall time from `4.90 m` for the
    horizontal range. Normalize these steps to the declared exact expression,
    then prove its `4.0±0.05 m` bound with certified radical and `π` bounds.

51. **`PhyXMiniProblems/problem_phyx_mini_0256.lean`.** Derive the series
    stiffness `k/2`, rewrite the Physlib oscillator frequency, and cancel
    positive `2π` to get the exact cyclic-frequency expression. Bound the
    square root and `π` tightly enough for the `18.2±0.05 Hz` predicate.

52. **`PhyXMiniProblems/problem_phyx_mini_0257.lean`.** Rewrite the Physlib
    period as `2π/√(k/m)`, use `W=mg` to infer the mass from the stated
    weight, and substitute `k=120`. Certified square-root and `π` intervals
    should prove the `0.686±0.0005 s` rounding and strict closest-choice
    inequalities; the equilibrium incline data need not enter the period.

53. **`PhyXMiniProblems/problem_phyx_mini_0258.lean`.** At the slip verge,
    equate required friction `mω²A` to `μ_smg`, substitute
    `ω²=k/(M+m)`, and cancel the positive upper mass to obtain the stated
    amplitude formula. Insert all rational readouts, convert to centimeters,
    and close the `23±0.5 cm` interval exactly.

54. **`PhyXMiniProblems/problem_phyx_mini_0259.lean`.** Read the graph peak
    energy and turning amplitude, use `K_max=½kA²`, and cancel the positive
    amplitude square to derive `k=2500/3`. Rewrite the target with this exact
    value and prove rounding plus unique closeness to `830` by rational
    absolute-value arithmetic.

55. **`PhyXMiniProblems/problem_phyx_mini_0260.lean`.** Eliminate the
    post-impact speed between momentum and post-embedding energy to prove the
    squared-amplitude relation. Use amplitude nonnegativity and positive
    stiffness/mass to select the stated square-root expression, then bound it
    inside the nearest-millimeter interval for choice C.

56. **`PhyXMiniProblems/problem_phyx_mini_0261.lean`.** Evaluate the
    pre-collision trajectory at `T/4` to get `x=-0.01`, `v=0`, apply
    sticking-collision momentum for common speed `4`, and expand Physlib's
    amplitude-from-initial-conditions formula. Rewrite the post-collision
    oscillator frequency from its mass/stiffness and certify the displayed
    amplitude interval.

57. **`PhyXMiniProblems/problem_phyx_mini_0262.lean`.** Sum the rod inertia,
    disk centroidal inertia, and disk parallel-axis term, and similarly sum
    the gravitational moments to derive the displayed compound-pendulum
    formula. Substitute the readouts and prove the period rounding and
    closest-choice statements with radical and `π` intervals.

58. **`PhyXMiniProblems/problem_phyx_mini_0263.lean`.** Derive the T-stick
    center of mass, pivot inertia, and restoring coefficient from the
    equal-stick idealization, then substitute them into the linearized
    oscillator law to get `2π√(5L/(6g))`. Evaluate at the source readouts and
    certify the `1.83 s` rounding and choice comparisons.

59. **`PhyXMiniProblems/problem_phyx_mini_0264.lean`.** Rewrite the
    linearized disk-pendulum law using `I=MR²/2+Md²` and restoring coefficient
    `Mgd`, cancel the positive mass, and obtain the stated formula. Substitute
    `R,d,g`, then use certified bounds to prove `0.366 s` rounding and
    closest choice C.

60. **`PhyXMiniProblems/problem_phyx_mini_0265.lean`.** Complete the square
    or compare `d+ρ²/d` using positivity to prove the radius of gyration is
    the global period minimizer. Rewrite the rectangle data for the exact
    radical, certify its `0.16 m` display bounds, and use the supplied
    face-geometry inequalities to show the entire metric circle is admissible
    and minimizing.

61. **`PhyXMiniProblems/problem_phyx_mini_0266.lean`.** Differentiate or use
    AM-GM on the uniform-rod period squared
    `(L²/12+x²)/(gx)` to prove the unique positive minimizer
    `L/(2√3)` and its `IsLeast` property. Substitute `L=1.85`, bound the
    closed-form period near `2.1 s`, and compare all displayed choices.

62. **`PhyXMiniProblems/problem_phyx_mini_0267.lean`.** Obtain the torque
    derivative at equilibrium from the conservative energy derivative, then
    rewrite corner radius, cube inertia, and torsional stiffness to cancel
    the edge length and derive `ω²=3k/m`. Select the positive square root,
    derive the period formula, and certify its recorded display interval.

63. **`PhyXMiniProblems/problem_phyx_mini_0268.lean`.** Combine the
    linearized extension, Hooke force, and lever arm to prove `κ=kr²`, then
    rewrite `r=L/2` and `I=mL²/12` in the generalized oscillator. Cancel
    positive factors to get `T=2π√(m/(3k))` and prove the four-decimal
    choice-C rounding from certified bounds.

64. **`PhyXMiniProblems/problem_phyx_mini_0269.lean`.** Derive `κ=kr²`
    from the plate geometry, rewrite the oscillator period and square it
    using positivity to solve `I=kr²T²/(4π²)`. Insert the graph/readout data,
    bound `π²`, and prove choice C is uniquely closest to the exact inferred
    inertia.

65. **`PhyXMiniProblems/problem_phyx_mini_0270.lean`.** Solve the connected
    generalized-oscillator period for
    `κ_s=I(2π/T_with)²-κ_g`, using positive periods before clearing
    denominators. Derive the disk pivot inertia and gravitational lever arm
    from the figure, substitute both periods, and certify the
    `18.5±0.05 N·m/rad` interval and uniqueness.

66. **`PhyXMiniProblems/problem_phyx_mini_0271.lean`.** Compare the three-car
    and two-car Hooke equilibrium equations to get the new `0.100 m`
    extension. Rewrite Physlib's amplitude from the post-break initial
    conditions; zero release velocity reduces it to the absolute equilibrium
    shift `|0.150-0.100|=0.050 m`, exactly choice C.

67. **`PhyXMiniProblems/problem_phyx_mini_0272.lean`.** Rewrite
    `κ=kr²`, hoop inertia `I=mR²`, and the rim attachment `r=R`; cancel the
    positive radius square to derive `ω²=k/m`. Since both the physical
    frequency and displayed square root are nonnegative, identify their
    positive roots and unfold choice C.

68. **`PhyXMiniProblems/problem_phyx_mini_0273.lean`.** Chain the SHM graph
    period, circular-motion correspondence, and centripetal law to derive
    `a_r=(2π/T)²A`. Insert `A=0.07 m`, `T=0.040 s`, normalize the exact
    expression, and bound it within `50 m/s²` of `1700`.

69. **`PhyXMiniProblems/problem_phyx_mini_0274.lean`.** Substitute the two
    kinetic-energy graph points into exact pendulum energy conservation and
    solve for the positive length
    `3/(392(1-cos 0.1))`. Prove the denominator positive and bound
    `cos 0.1` by its alternating Taylor series tightly enough for the
    `1.53±0.005 m` and unique-choice claims.

70. **`PhyXMiniProblems/problem_phyx_mini_0275.lean`.** Derive
    `k=F/A=250` from the force-displacement endpoint, construct the maximum
    kinetic energy at equilibrium using energy conservation and nonnegative
    potential energy, and compute `45/4 J`. Unfold the half-open tenth
    rounding convention to show `11.25` rounds upward to `11.3` and compare
    all choices.

71. **`PhyXMiniProblems/problem_phyx_mini_0276.lean`.** Reduce the
    disk-pendulum period equation to its quadratic in the pivot-to-center
    distance, use the physical interval to select the displayed plus-root,
    and subtract the radius to obtain rod length. Certify the discriminant,
    radical, and `π` bounds required for the nearest-tenth-millimeter and
    closest-choice conclusions.

72. **`PhyXMiniProblems/problem_phyx_mini_0277.lean`.** From the acceleration
    graph derive `cos φ=-1/4`; use the positive graph slope and the derivative
    law to prove the phase is in quadrant II. Identify
    `φ=arccos(-1/4)` by cosine injectivity, then certify its
    `1.82±0.005` interval and closest-choice comparisons.

73. **`PhyXMiniProblems/problem_phyx_mini_0278.lean`.** Rewrite angular
    velocity as the derivative of the sinusoidal angle trace, use
    `|sin|≤1` and an explicit quarter-period witness to prove the range
    maximum `Aω=π`. Apply a standard rational interval for `π` to show it
    lies within `0.005` of `3.14`.

74. **`PhyXMiniProblems/problem_phyx_mini_0279.lean`.** Compute initial
    spring energy `3/32`, rewrite solid-cylinder rotational energy with
    `I=MR²/2` and rolling `v=Rω`, and combine it with translational energy to
    show the rotational share is one third. Normalize to `1/32 J` and unfold
    exact displayed choice D.

75. **`PhyXMiniProblems/problem_phyx_mini_0280.lean`.** Use the Physlib
    trajectory energy invariant and release-at-amplitude data to show every
    kinetic energy is bounded by the initial spring energy, with equality at
    equilibrium. Substitute `k=200`, `A=0.20` to get exactly `4 J`, then
    discharge answer agreement and unique closeness by cases.

76. **`PhyXMiniProblems/problem_phyx_mini_0281.lean`.** Square the positive
    spring and pendulum frequency laws under the frequency-match hypothesis;
    use the spring static balance `kh=mg` to show the pendulum length equals
    the equilibrium extension. Rewrite the stated `h=2 cm` and unfold exact
    answer D.

77. **`PhyXMiniProblems/problem_phyx_mini_0282.lean`.** Use the equal-period
    reversible-pendulum theorem to identify pivot separation with the
    equivalent simple-pendulum length `gT²/(4π²)`. Substitute `T=1.80`,
    `g=9.8`, bound `π²`, and prove the half-millimeter interval and strict
    uniqueness for `0.804 m`.

78. **`PhyXMiniProblems/problem_phyx_mini_0283.lean`.** Eliminate mass and
    parallel-cord stiffness between static balance and
    `a_max=ω²d_m` to derive `a_max d_s=g d_m`. Insert
    `a_max=0.20g` and `d_m=10 cm`, cancel positive gravity, and obtain
    exactly `d_s=50 cm`, choice D.

79. **`PhyXMiniProblems/problem_phyx_mini_0284.lean`.** Rewrite the
    small-angle period with `L=17 m` and standard gravity; the retained ball
    mass cancels. Prove a rational interval for `2π√(17/9.8)` inside
    `8.3±0.05 s` and show each other displayed tenth is strictly farther.

80. **`PhyXMiniProblems/problem_phyx_mini_0285.lean`.** Derive the propagation
    speed in seat-spacings per second from `853/39`, multiply by the
    `1.8 s` response duration to obtain the exact wave width, and use the
    characterization of `round` after proving it lies in `[38.5,39.5)`.

81. **`PhyXMiniProblems/problem_phyx_mini_0286.lean`.** Solve the two
    constant-speed travel equations and arrival-lag equation for
    `d=Δt/(1/v_t-1/v_l)`, with nonzero denominators from the physical speed
    inequalities. Substitute `50`, `150`, and `0.004` to get `0.30 m`,
    convert to `30 cm`, and unfold choice D.

82. **`PhyXMiniProblems/problem_phyx_mini_0287.lean`.** Combine
    `kλ=2π` and maximum slope `S_max=kA`, cancel positive `k`, and insert
    `λ=0.40`, `S_max=0.20` to derive `A=1/(25π)`. Bound the reciprocal of
    `π` to show four-decimal rounding to `0.0127 m` and eliminate the other
    choices.

83. **`PhyXMiniProblems/problem_phyx_mini_0288.lean`.** Differentiate the
    displacement law to establish the velocity normal form, then use the
    supplied global bound and attainment clauses to identify
    `u_max=ωA`. At the graph origin derive `cos φ=4/5` and use the
    acceleration sign to select quadrant IV, so
    `φ=-arccos(4/5)`; certify the `-0.64` display interval.

84. **`PhyXMiniProblems/problem_phyx_mini_0289.lean`.** Extract wave speed
    `0.06/0.004=15 m/s` and wavelength `0.40 m` from the two snapshots,
    then use `ω=2πv/λ` to obtain `75π`. Apply rational `π` bounds to prove
    the strict nearest-ten interval around `240`.

85. **`PhyXMiniProblems/problem_phyx_mini_0290.lean`.** Derive
    `ω=π/5`, `k=π/10` in centimeter/second units, and use the initial graph
    value plus rising slope to fix phase `π` for the right-moving convention.
    Evaluate the velocity law at `x=0,t=5` to get `-4π/5`, then bound it in
    the one-decimal choice-D interval.

86. **`PhyXMiniProblems/problem_phyx_mini_0291.lean`.** Read adjacent crests
    to get `λ=2/5 m`, derive `v=√(T/μ)=12 m/s`, and cancel positive speed in
    `λ=vP` to obtain `P=1/30 s`. Compare this exact rational with the four
    displayed millisecond values to prove D is nearest.

87. **`PhyXMiniProblems/problem_phyx_mini_0292.lean`.** Use movable-pulley
    balance and equal string-1 tensions to derive `49/20 N` per support, then
    transfer that tension through the massless knot. Substitute
    `μ₂=0.005` in `v=√(T/μ)` for `√490`, and prove its `22.1±0.05 m/s`
    interval by squaring.

88. **`PhyXMiniProblems/problem_phyx_mini_0293.lean`.** Read twice-adjacent
    peak spacings to obtain `λ=0.2 m` and `T=2 ms`, hence
    `v=100` and `ω=1000π`. Substitute these and the peak kinetic-energy
    transport rate into the wave-power law, solve the positive amplitude, and
    certify its four-decimal choice-D rounding.

89. **`PhyXMiniProblems/problem_phyx_mini_0294.lean`.** Prove the
    equal-amplitude sine sum by `ring_nf` plus `sin_add`/`cos_add`, use it to
    identify resultant amplitude
    `2A cos((φ₁-φ₂)/2)`, and derive `λ=40 cm`, speed `7 cm/ms`, and the
    leftward temporal sign. Insert the graph/readout amplitude ratio, select
    the permitted phase branch, and certify the resulting phase near choice C
    with inverse-cosine bounds.

90. **`PhyXMiniProblems/problem_phyx_mini_0295.lean`.** Use the fixed-end
    mode geometry to get the wavelength, then combine `v=fλ` with
    `T=μv²` and the positive-speed branch to derive
    `1250√3/9 Hz`. Square rational bounds on `√3` to place this in the
    `241±0.5 Hz` interval.

91. **`PhyXMiniProblems/problem_phyx_mini_0296.lean`.** Derive wavelength
    `0.40 m`, wave number `5π`, angular frequency `π`, phase offset `π`,
    and requested spatial phase `π` in that order. Substitute them into the
    differentiated standing-wave velocity law at the requested event,
    normalize exact trigonometric values, and bound the result in the
    `-0.13±0.005 m/s` interval.

92. **`PhyXMiniProblems/problem_phyx_mini_0297.lean`.** Use the
    consecutive-opposite-extrema observation to show `6 ms=T/2`, hence
    `T=12 ms`; substitute into `ω=2π/T` for `500π/3`. Certified bounds for
    `π` place it strictly within five radians per second of `520`.

93. **`PhyXMiniProblems/problem_phyx_mini_0298.lean`.** Specialize the
    fourth-harmonic fixed-end law with `L=1.20 m`, `f=120 Hz` to solve
    `v=72`. Use `T=μv²`, pulley tension equality, and static weight balance
    to derive mass `5184/6125`, then close the `0.846±0.0005 kg` comparison.

94. **`PhyXMiniProblems/problem_phyx_mini_0299.lean`.** Prove the second
    aluminum and fifth steel modes each lie within the declared whole-hertz
    window at `324`, using exact radical/rational bounds for their wave
    speeds. For an arbitrary lower joint-node candidate, extract both mode
    indices and use their positive lower constraints and interval
    incompatibility to prove it cannot be below `324`.

95. **`PhyXMiniProblems/problem_phyx_mini_0300.lean`.** Divide the initial
    displacement by positive amplitude to get `sin φ=1/3`; use the rising
    trace with the `-ωt` convention to prove `cos φ<0`. The principal phase
    is therefore `π-arcsin(1/3)`; certify its `2.8±0.05` interval and the
    non-strict closest-choice comparisons.

96. **`PhyXMiniProblems/problem_phyx_mini_0302.lean`.** Differentiate the
    sinusoidal displacement twice for the acceleration normal form and once
    more for the stated time derivative. Use the bound/attainment fields to
    derive maximum acceleration `ω²A`, infer the phase branch from the graph
    ordinate and descending sign, and certify the requested displayed
    acceleration and answer choice with rational trig bounds.

97. **`PhyXMiniProblems/problem_phyx_mini_0304.lean`.** Rewrite dent radius
    as `depth·tan(coneHalfAngle)` using the conical geometry and substitute
    the collision/longitudinal-front readouts that determine depth. Prove a
    certified tangent interval giving radius within `0.001 m` of `0.01`,
    then show that interval is strictly closer to D than A–C.

98. **`PhyXMiniProblems/problem_phyx_mini_0305.lean`.** Derive
    `ω=π/2` and `k=π/10 cm⁻¹`, then use derivative uniqueness plus
    speed bound/attainment to show `u_max=ωA`. Solve from the graph's
    `u_max=5 cm/s` for `A=10/π cm`, convert as needed, and certify the
    displayed amplitude rounding.

99. **`PhyXMiniProblems/problem_phyx_mini_0306.lean`.** Use centripetal
    acceleration and rotating-loop force balance to derive
    `T=μv_t²`; compare with `T=μc²`, cancel positive density, and use
    nonnegativity to turn equality of squares into `c=v_t`. Rewrite the
    `5.00 cm/s` readout and choice D.

100. **`PhyXMiniProblems/problem_phyx_mini_0307.lean`.** Solve
     `(A+B)/(A-B)=3/2` for `B/A=1/5`, with denominator signs supplied by the
     physical amplitude ordering. Square that ratio in the common-medium
     power law to get reflection coefficient `1/25`, then normalize its
     percentage to `4` and prove the answer iff by cases.

101. **`PhyXMiniProblems/problem_phyx_mini_0308.lean`.** Rewrite the exact
     path-difference equality into the requested speed-weighted sine identity.
     Subtract its zero-residual form, apply `abs_mul` with positive calibrated
     sound speed, and use the stored residual bound to derive the explicit
     error inequality; do not assert the unsupported historical `13°`
     metadata.

102. **`PhyXMiniProblems/problem_phyx_mini_0309.lean`.** Read the graph
     period as `2 ms`, convert it to `500 Hz`, and derive `ω=1000π`.
     Substitute standard sound speed into `ω=kv` for `k=1000π/343`, then use
     rational `π` bounds to establish the displayed wave-number interval and
     answer selection.

103. **`PhyXMiniProblems/problem_phyx_mini_0310.lean`.** Derive the adjacent
     round-trip increment `2w`, divide by positive sound speed for pulse
     period `3/686 s`, and take its positive reciprocal to get `686/3 Hz`.
     Exact rational absolute-value comparisons make `230 Hz` the unique
     closest choice.

104. **`PhyXMiniProblems/problem_phyx_mini_0311.lean`.** Reduce exact phase
     opposition to positive odd half-integers by the propagation/reflection
     law and principal phase equivalence. Prove `1/2` is the least solution
     and any solution below `3/2` equals `1/2`, establishing the custom
     `IsSecondSmallest` predicate; unfold recorded choice D separately.

105. **`PhyXMiniProblems/problem_phyx_mini_0312.lean`.** Parameterize
     out-of-phase detector points by the seven admissible positive odd
     half-wavelength path-difference magnitudes and the two symmetric circle
     intersections for each. Prove the parametrization is a bijection,
     compute `ncard=2·7=14`, and eliminate A–C by their distinct finite
     displayed counts.

106. **`PhyXMiniProblems/problem_phyx_mini_0313.lean`.** Derive whole-
     wavelength path differences from the equal spacing, rewrite propagation
     phases modulo full turns to show all four arrivals agree, and evaluate
     the finite phasor sums by enumerating `SourceLabel`. Use
     `sin²+cos²=1`, common-amplitude positivity, and `sqrt_sq` to obtain net
     amplitude `4s_m` and the matching displayed choice.

107. **`PhyXMiniProblems/problem_phyx_mini_0314.lean`.** Use Pythagoras for
     upper path `17/4 m`, subtract the lower `15/4 m` for path difference
     `1/2`, and specialize constructive order three to get `f=6v`. With
     `v=343`, prove the requested frequency is `2058 Hz`, enumerate lower
     audible orders, and discharge the theorem's explicit non-match with all
     recorded choices rather than forcing `1029 Hz`.

108. **`PhyXMiniProblems/problem_phyx_mini_0315.lean`.** Derive
     `ΔL=(π-2)r` from semicircle versus diameter geometry. At the least
     destructive order set `ΔL=λ/2=20 cm`, construct
     `r=20/(π-2)`, and show every other positive destructive order is no
     smaller; then bound this quotient in the `17.5±0.05 cm` interval.

109. **`PhyXMiniProblems/problem_phyx_mini_0316.lean`.** Square the
     perpendicular-path relation after proving all lengths nonnegative, set
     path difference to `3λ/2=3`, and solve uniquely for `x=247/6`.
     Prove the requested set extensional equality and close choice D's
     one-decimal rounding and uniqueness by rational arithmetic.

110. **`PhyXMiniProblems/problem_phyx_mini_0317.lean`.** Divide the two
     inverse-square laws at any common radius, using positive intensities and
     radii, to show the intensity ratio and logarithmic decibel difference
     are radius independent. Read the graph's one-grid-step difference as
     `5 dB`, transport it from `100 m` to `10 m`, and compare the four
     displayed choices.

111. **`PhyXMiniProblems/problem_phyx_mini_0318.lean`.** Convert
     `L=45.7 cm`, specialize the open-open fourth-mode formula for
     `688000/457 Hz`, and bound the harmonic spacing to show modes 3, 4, 5
     are exactly the in-sweep order. Prove mode 4 rounds to `1505`, not the
     recorded `1506`, and eliminate every printed choice under the stated
     strict half-hertz predicate.

112. **`PhyXMiniProblems/problem_phyx_mini_0319.lean`.** Compose the outbound
     moving-source/observer Doppler factor, rest-frame reflection, and inbound
     factor, then insert the four speed/frequency readouts. Normalize the
     result to `2548400/2439` and prove its strict `1045±0.5 Hz` interval,
     yielding choice D.

113. **`PhyXMiniProblems/problem_phyx_mini_0320.lean`.** Rewrite tube 4's
     third-harmonic emission and the receding-detector Doppler law in the
     tuning condition, cancel positive fundamental frequency and sound speed,
     and solve the factor equation for detector speed `2c/3`. Prove both
     directions and unfold the NNReal scalar choice D.

114. **`PhyXMiniProblems/problem_phyx_mini_0321.lean`.** Combine the
     two-leg echo distance with constant-speed travel, cancel `2`, and derive
     `L=vΔt/2`. Insert `1372 m/s` and `3 ms` to get `1029/500 m`; exact
     rational arithmetic proves the `2.1±0.05 m` display interval.

115. **`PhyXMiniProblems/problem_phyx_mini_0322.lean`.** Convert like
     reflection phases to an integral number of cycles and the two extra legs
     to path excess `2L`. The least positive odd half-cycle therefore gives
     `L=λ/4`; prove the iff with the leastness predicate, then unfold choice D
     and show no other displayed multiple equals `1/4`.

116. **`PhyXMiniProblems/problem_phyx_mini_0323.lean`.** Solve the exact
     reflected/direct in-phase path equation on the positive branch for
     `sqrt(λ(4L+λ))/4`, and prove it is least using monotonicity of the path
     difference. Bound the radical so that `round (100x)=147`, then discharge
     the unique displayed answer by cases.

117. **`PhyXMiniProblems/problem_phyx_mini_0324.lean`.** Solve the pulse-echo
     Doppler law at the peak-shift phase for
     `v=5495·1540/(2·5,000,000·cos20°)`, using positivity of the acute-angle
     cosine. Transport the maximum frequency-shift hypothesis to a maximum
     speed inequality and certify the `0.90±0.005 m/s` choice-D interval with
     a cosine bound.

118. **`PhyXMiniProblems/problem_phyx_mini_0326.lean`.** Chain impact energy,
     surface-wave fraction, impact duration, cylindrical wavefront area, and
     lossless intensity to derive the mass-dependent formula. Substitute all
     fixed readouts and the two allowed mass endpoints, preserve monotonicity
     in mass to get the exact intensity interval, and prove that interval is
     disjoint from recorded D's `58±0.5 kW/m²` window.

119. **`PhyXMiniProblems/problem_phyx_mini_0327.lean`.** Algebraically solve
     the two-leg Doppler ratio for target speed
     `343(22.2-18)/(22.2+18)`, using positive denominators and the approaching
     branch. Normalize to `2401/67`, then prove strict rounding to `35.84`
     and unfold choice D.

120. **`PhyXMiniProblems/problem_phyx_mini_0328.lean`.** Apply the
     adjacent-node law to the marked cork ridges for `λ=2·9.20 cm=0.184 m`,
     then use `v=λf` with the drive readout to compute the exact sound speed.
     Normalize units and prove its nearest-whole-meter-per-second interval
     uniquely selects D.

121. **`PhyXMiniProblems/problem_phyx_mini_0329.lean`.** Write the reflected
     two-leg path at heights `H` and `H+h`, subtract the two square-root
     lengths, and use the first-opposition observation to set that change to
     `λ/2`. Solve in every length unit for the displayed factor-two formula
     and prove syntactic/exact uniqueness of symbolic choice D.

122. **`PhyXMiniProblems/problem_phyx_mini_0332.lean`.** Subtract the
     temperature readouts to obtain `ΔT=80 K`, substitute this and
     `c=4190` into `q/m=cΔT`, and normalize to `335200 J/kg`. Evaluate the
     four absolute differences exactly to show `340000` (A) is uniquely
     closest.

123. **`PhyXMiniProblems/problem_phyx_mini_0334.lean`.** Derive the
     pressure-headspace product from Boyle's law after canceling the positive
     tank area, combine it with the atmospheric outlet balance, and insert
     the data to obtain `49h²-745h+1146=0`. Factor or use the quadratic
     formula, reject the root outside the physical decreasing-height interval,
     and prove the remaining root's displayed rounding and answer choice.

124. **`PhyXMiniProblems/problem_phyx_mini_0335.lean`.** Use midpoint
     geometry to get `r=d/2`, enumerate the two atom sites in the point-mass
     inertia sum, and simplify to `md²/2`. Insert the SI mass and bond length
     conversions for `406456/10^51`, then prove the half-resolution choice-A
     interval and unique closeness exactly.

125. **`PhyXMiniProblems/problem_phyx_mini_0336.lean`.** For each graph
     vertex rewrite the ideal-gas law as `n=PV/(RT)` with common positive
     `R` and the vertex temperature. Evaluate the four rational readouts,
     prove the upper-right value dominates, and place it strictly within
     `0.0005 mol` of recorded answer B.

126. **`PhyXMiniProblems/problem_phyx_mini_0337.lean`.** Evaluate the
     vertical `a→b` work as zero and the straight `b→c` work as average
     pressure times volume change, including the liter-atmosphere to joule
     conversion, to obtain `4053/25`. Substitute into
     `ΔU=Q-W` for `1322/25` and prove nearest-joule rounding to `53`.

127. **`PhyXMiniProblems/problem_phyx_mini_0338.lean`.** Compute the
     straight `ab` leg by the trapezoid pressure formula, the isochoric `bc`
     leg as zero, and sum to `21000 J`. Apply the first law with the stated
     internal-energy increase to get heat `36000 J`; the recorded-choice
     theorem then follows by unfolding B.

128. **`PhyXMiniProblems/problem_phyx_mini_0342.lean`.** Evaluate work on
     the constant-pressure `a→c` leg, use the adiabatic relation and endpoint
     data for the curved `c→b` work, and set the constant-volume `b→a` work
     to zero. Sum the directed cycle contributions and certify the resulting
     exact/rational interval lies within `5 J` of `-1950 J`.
