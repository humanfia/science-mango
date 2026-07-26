# Iteration 019 Plan

## Batch contract

- Preserve exactly the 128 loop-selected Current Objectives below, in their
  existing order: three mandatory proof-Review retries followed by 125 new
  accepted-open targets. No `proof_review_exhausted` target is present.
- Eligibility shortfall: 0. Execution should keep exactly 32 distinct proof
  lanes occupied while draining this fixed ordered list, dispatching the three
  retries first. Plan does not truncate, reorder, or otherwise mutate the
  loop-selected objectives.
- Preserve every theorem statement and physical hypothesis. Derive exact
  physical relations before answer-choice predicates; prove denominator,
  orientation, and square-root branch conditions explicitly; certify every
  trigonometric, logarithmic, `pi`, radical, and rounding bound used.
- The supplied blueprint excerpts expose no concrete chapter-level strategy
  defect, so no blueprint chapter is changed. In `0546`, the auxiliary
  regularization lemma is false under `ContinuousAt` alone because its Bochner
  integral also needs measurability; keep that irreducible gap explicit rather
  than strengthening a frozen hypothesis or using an escape hatch.

## Per-target proof strategy

1. **`PhyXMiniProblems/problem_phyx_mini_0544.lean` (retry; 2/3 used).**
   Re-elaborate the existing boundary-matching derivation with named nonzero
   wave-number and square-root denominators, obtain the amplitude ratio by
   cross-multiplication, and normalize the final flux ratio with `field_simp`
   and `ring`; finish the choice conjunct by unfolding only its display
   predicate.

2. **`PhyXMiniProblems/problem_phyx_mini_0546.lean` (retry; 2/3 used).**
   Recheck the approximate-identity route against the frozen hypotheses.
   `ContinuousAt` at the center does not imply the a.e. strong measurability
   required by the Bochner integral, so retain the single honest `sorry` in
   `centered_rectangular_regularization_tends_to_dirac`; do not disturb the
   independently provable ground-state and first-order-energy results.

3. **`PhyXMiniProblems/problem_phyx_mini_0676.lean` (retry; 1/3 used).**
   Stabilize the existing tangent estimate by isolating the cubic identity and
   proving its comparison factor positive at both rational endpoints; derive
   `1399/2000 < tan θ < 1401/2000`, scale to the width interval, and discharge
   the four finite closest-choice cases by rational arithmetic.

4. **`PhyXMiniProblems/problem_phyx_mini_0753.lean`.**
   Rewrite the horizontal projectile law and circular tangent-speed readouts
   to solve the positive flight time, then substitute it into the vertical
   law. Reduce `sin (π/6)` and `cos (π/6)` exactly and certify `pi`/`sqrt 3`
   bounds sufficient for the `2.64 m` rounding and uniqueness comparisons.

5. **`PhyXMiniProblems/problem_phyx_mini_0754.lean`.**
   Prove the cab derivative with the constant-function derivative rule, obtain
   the relative-velocity derivative by subtracting it from the ball derivative,
   and simplify the absolute value using positivity of gravitational
   acceleration before checking the displayed choices by `norm_num`.

6. **`PhyXMiniProblems/problem_phyx_mini_0755.lean`.**
   Rewrite the three force vectors from the readout and direction laws, compute
   the resultant norm square by `ring`, divide by the positive mass, and select
   the nonnegative square-root branch. Bound the remaining radical tightly
   enough to prove rounding to `0.88` and strict separation from every other
   choice; assemble the target from the two helper lemmas.

7. **`PhyXMiniProblems/problem_phyx_mini_0756.lean`.**
   Project static equilibrium onto the two figure axes, use the Alex–Betty
   `137°` geometry and Charles’s upper-right quadrant to exclude the reflected
   solution, and eliminate the other unknown pull. Certify the needed
   degree-trigonometric bounds, then prove the requested Betty magnitude and
   its displayed-choice predicate.

8. **`PhyXMiniProblems/problem_phyx_mini_0757.lean`.**
   Specialize the disk-C vertical equilibrium law, rewrite `T₂ = 49`,
   `T₃ = 9.8`, and `g = 9.8`, and use positivity of mass with `linarith`/`norm_num`
   to obtain `m_C = 4`; unfold the finite answer table and prove uniqueness by
   cases.

9. **`PhyXMiniProblems/problem_phyx_mini_0758.lean`.**
   Sum the six identical upward tension components and cancel the positive
   weight to derive `T/W = 1/(6 sin 40°)` for each leg. Prove `sin 40° > 0`,
   certify a narrow sine interval, and convert it into the `0.26` display
   tolerance for the recorded choice.

10. **`PhyXMiniProblems/problem_phyx_mini_0759.lean`.**
    Eliminate the horizontal push from the two zero-acceleration component
    balances, justify division by positive `cos θ`, and specialize
    `cos 30° = sqrt 3/2`. Use rational bounds for `sqrt 3` to prove the exact
    `1960*sqrt 3/3` force is uniquely closest to choice C.

11. **`PhyXMiniProblems/problem_phyx_mini_0760.lean`.**
    Derive the water-force components directly from Newton’s law, then use the
    supplied direction law and certified bounds for `sin 18°` and `cos 18°` to
    place its angle in a sub-degree interval around `201°`. Reduce circular
    angle distances for all four choices inside a common principal interval.

12. **`PhyXMiniProblems/problem_phyx_mini_0762.lean`.**
    Cross-multiply the cab-B and box force equations, cancel the positive common
    mass/acceleration factors, and substitute the three rational readouts to
    obtain `2292/13`. Unfold rounding and the finite answer table; all remaining
    inequalities are rational `norm_num`.

13. **`PhyXMiniProblems/problem_phyx_mini_0763.lean`.**
    Solve collision momentum for the block’s `2 m/s` speed, equate post-impact
    kinetic energy with turning-point spring energy, and use nonnegative
    compression to select `sqrt (3/25)`. Square rational endpoints to certify
    the nearest-millimetre answer and finish the target from the helpers.

14. **`PhyXMiniProblems/problem_phyx_mini_0764.lean`.**
    Apply sticking-collision momentum conservation to obtain the compound
    `6 m/s` speed, substitute it into frictionless ascent energy, and cancel the
    positive total mass to derive `90/49 m`. Compare that rational exactly with
    all displayed heights, retaining physical choice C rather than inconsistent
    dataset metadata.

15. **`PhyXMiniProblems/problem_phyx_mini_0765.lean`.**
    Prove in sequence the static spring calibration, free-fall speed square,
    `4/7` sticking-speed ratio, and the displacement quadratic. Show the
    physical displacement is nonnegative, exclude the negative quadratic root,
    then certify the positive radical’s rounding interval and assemble the six
    obligations without conserving energy across the collision.

16. **`PhyXMiniProblems/problem_phyx_mini_0766.lean`.**
    Combine swing energy, sticking momentum, and friction work to cancel both
    intermediate speeds and gravity, yielding the mass-ratio identity. Insert
    the positive readouts, solve for `256/45 m`, and prove the nearest-tenth
    predicate for displayed answer B by rational arithmetic.

17. **`PhyXMiniProblems/problem_phyx_mini_0767.lean`.**
    Derive `v_before² = 2gR`, use equal-mass momentum to obtain
    `v_after = v_before/2`, and apply post-collision ascent energy to show the
    rise is the corresponding exact fraction of `R`. Cancel only positive mass,
    gravity, and radius factors, then unfold the displayed coefficient table.

18. **`PhyXMiniProblems/problem_phyx_mini_0768.lean`.**
    Preserve the package’s horizontal velocity through projectile motion,
    substitute it into signed horizontal momentum conservation, and prove the
    resulting common velocity is negative. Use certified `cos 37°` bounds to
    bound its speed, establish the hundredth-place answer, and separate all
    alternatives.

19. **`PhyXMiniProblems/problem_phyx_mini_0769.lean`.**
    Expand rigid-canoe kinematics inside the conserved center-of-mass equation
    and solve the resulting linear relation for signed displacement `-9/7`.
    Simplify its absolute value using negativity, then prove the `1.29` rounding
    and four-case closest-choice result with rational arithmetic.

20. **`PhyXMiniProblems/problem_phyx_mini_0770.lean`.**
    Rewrite translational and rotational energies, eliminate angular speed with
    no slip and the pulley inertia law, and solve the positive-distance energy
    equation for `33/49 m`. The three-decimal match to `0.673` is a direct
    rational absolute-value calculation.

21. **`PhyXMiniProblems/problem_phyx_mini_0771.lean`.**
    Solve the constant-acceleration endpoint equation using nonzero elapsed
    time, then eliminate tension and angular acceleration from translation,
    rotation, no-slip, and uniform-disk inertia to obtain
    `M = 2m(g/a - 1)`. Substitute SI readouts and prove the finite nearest-mass
    comparisons.

22. **`PhyXMiniProblems/problem_phyx_mini_0772.lean`.**
    Calibrate the linear acceleration slope to `3/5`, integrate the no-slip
    angular-acceleration profile, and use positivity to select event time
    `5*sqrt 2/2`. Integrate angular velocity once more for the event angle,
    simplify powers of `sqrt 2`, and compare the exact angle with the displayed
    choices.

23. **`PhyXMiniProblems/problem_phyx_mini_0773.lean`.**
    Use the Earth energy balance to obtain `485 J` and speed square `194/3`;
    prove equal drum rotational energies imply equal rim and mass speed squares
    via no slip and positive inertia/radius. Select the positive Mars speed
    root and certify its displayed rounding before assembling the five results.

24. **`PhyXMiniProblems/problem_phyx_mini_0774.lean`.**
    Reduce the Physlib tensor contraction along the fixed pulley axis to
    `Iω²/2`, substitute the no-slip and mechanical-energy laws, and normalize
    the readouts to derive `v² = 6272/667`. Use speed nonnegativity plus
    `Real.sq_sqrt`, then square rational endpoints to establish the displayed
    speed.

25. **`PhyXMiniProblems/problem_phyx_mini_0775.lean`.**
    Add the two disk inertias to `9/4000`, eliminate angular speed from energy
    with the smaller-disk no-slip radius, and derive the effective-mass speed
    formula. Normalize it to `v² = 196/17`, select the positive root, and prove
    the `3.40 m/s`-scale display comparison by squared rational bounds.

26. **`PhyXMiniProblems/problem_phyx_mini_0777.lean`.**
    Expand each planar torque using the square geometry and force directions,
    reduce exact `45°` trigonometry, and sum signed contributions to
    `18/25 + (63/50)sqrt 2`. Prove positivity and the `2.50` rounding with
    elementary rational bounds for `sqrt 2`.

27. **`PhyXMiniProblems/problem_phyx_mini_0778.lean`.**
    Eliminate both tensions and pulley angular acceleration from the three
    dynamics equations, replace `I/r²` by half the pulley mass, and solve for
    `a = 49/18`. Reuse that equality in the target and discharge the `2.72`
    tolerance by `norm_num`.

28. **`PhyXMiniProblems/problem_phyx_mini_0779.lean`.**
    Rewrite the hoop inertia and no-slip laws in the conserved-energy equation
    so translational and rotational kinetic energies combine to `m v²`.
    Cancel positive mass, select `sqrt (gh)`, specialize to `sqrt (147/20)`,
    and prove rounding/uniqueness by squaring positive decimal endpoints.

29. **`PhyXMiniProblems/problem_phyx_mini_0780.lean`.**
    Substitute the hollow-cylinder inertia and no-slip relation into the
    release-to-target energy law, cancel positive mass and radius factors, and
    solve exactly for `2008323/534100 m`. Both theorem-level answer predicates
    then reduce to rational nearest-hundredth inequalities.

30. **`PhyXMiniProblems/problem_phyx_mini_0781.lean`.**
    Compute the disk inertia `169/100`, convert `120 rev/min` exactly to
    `4π rad/s`, and obtain angular acceleration `-650/169` from the signed axle
    torque. Solve the stopping equation for time and use certified `pi` bounds
    to prove its nearest-hundredth answer.

31. **`PhyXMiniProblems/problem_phyx_mini_0782.lean`.**
    Normalize the inertia and energy equations to `ω² = 3675/113`, use angular
    speed nonnegativity to select `sqrt (3675/113)`, and square tight rational
    bounds around `5.70`. Enumerate the answer type to prove the selected value
    is uniquely closest.

32. **`PhyXMiniProblems/problem_phyx_mini_0783.lean`.**
    Eliminate the two tensions and common linear acceleration from the Atwood
    component equations, wheel torque, and no-slip constraint to prove the
    unit-generic formula. Specialize SI readouts to `2940/383` and finish the
    `7.68` display tolerance by exact rational arithmetic.

33. **`PhyXMiniProblems/problem_phyx_mini_0784.lean`.**
    Rewrite the force and acceleration readouts in Newton’s second law, solve
    the resulting scalar equation for the unrounded `1302 N`, and unfold the
    four displayed values. Exact absolute-error comparisons show `1300 N`
    (choice B) is uniquely closest.

34. **`PhyXMiniProblems/problem_phyx_mini_0785.lean`.**
    Use normal balance to rewrite kinetic friction, eliminate linear and angular
    accelerations through no slip, and substitute the rotational inertia law to
    derive the general string-tension formula. Normalize the supplied numbers
    to `14 N` and prove exact uniqueness by cases on the answer label.

35. **`PhyXMiniProblems/problem_phyx_mini_0787.lean`.**
    Combine rolling energy, no slip, and shell inertia to show translational
    energy is `3/5` of the initial potential energy. On the smooth ascent keep
    rotational energy constant, equate the remaining translational energy to
    final potential energy, cancel positive `mg`, and select coefficient B.

36. **`PhyXMiniProblems/problem_phyx_mini_0788.lean`.**
    Derive the cliff-edge speed square from rolling energy, specialize it to
    `233`, then combine projectile vertical drop with retained rotation to
    eliminate the intermediate speed and obtain the landing-speed square.
    Select positive roots and certify both requested numerical/choice
    predicates by squared rational bounds.

37. **`PhyXMiniProblems/problem_phyx_mini_0789.lean`.**
    Expand the solid-sphere rolling energy over the rough half, preserve its
    rotational kinetic energy over the torque-free ice half, and cancel the
    positive mass to derive bottom translational speed square `840`. Use speed
    nonnegativity and square bounds around `29.0` for the unique choice.

38. **`PhyXMiniProblems/problem_phyx_mini_0791.lean`.**
    Subtract the two image bearings to obtain the `77°` included angle, apply
    `InnerProductGeometry.cos_angle_mul_norm_mul_norm`, and substitute magnitudes
    `4` and `5`. Prove a sufficiently sharp certified bound for `cos 77°` to
    establish rounding to `4.50`.

39. **`PhyXMiniProblems/problem_phyx_mini_0793.lean`.**
    Solve the velocity endpoint equation for elapsed time `5/2 s`, substitute
    it into constant-acceleration displacement, and normalize to the signed
    position `55 m`. Unfold the finite answer table and prove choice uniqueness
    by `decide`/`norm_num` after rewriting the physical equality.

40. **`PhyXMiniProblems/problem_phyx_mini_0796.lean`.**
    Eliminate positive flight time to obtain the usual
    `R = v² sin(2θ)/g` formula. Use `sin x ≤ 1`, exact equality at `π/4`, and
    the admissible-angle interval to prove maximality and uniqueness; evaluate
    the four displayed angles to select choice B.

41. **`PhyXMiniProblems/problem_phyx_mini_0797.lean`.**
    Rewrite the north/east velocity components, compute the squared Euclidean
    norm as `240² + 100² = 260²`, and select the nonnegative norm branch.
    Substitute the resulting `260 km/h` into the display predicate.

42. **`PhyXMiniProblems/problem_phyx_mini_0798.lean`.**
    Rearrange the work–energy equation between the two endpoints, use positive
    stopping distance to solve for friction magnitude, and substitute the
    printed mass/speed/distance values. Normalize to exactly `0.90 N` and close
    the recorded-choice equality by unfolding definitions.

43. **`PhyXMiniProblems/problem_phyx_mini_0799.lean`.**
    Project static equilibrium perpendicular to the incline; the cable has no
    normal component, so solve directly for `N = w cos α` in every coherent
    unit system. Rewrite the choice-B expression with this result and prove
    finite uniqueness by simplifying the other symbolic formulas.

44. **`PhyXMiniProblems/problem_phyx_mini_0800.lean`.**
    Reduce constant-speed kinematics to zero acceleration, derive separate
    cart and bucket force balances, and eliminate the common tension to obtain
    `w₂ = w₁ sin 15°`. The final answer predicate follows by unfolding choice B
    and reusing the exact balance.

45. **`PhyXMiniProblems/problem_phyx_mini_0801.lean`.**
    Solve the velocity law for acceleration `3/2`, substitute it into the
    frictionless horizontal Newton law with mass `200`, and derive the signed
    wind force `300 N`. Unfold all four displayed forces to prove exact match
    and uniqueness.

46. **`PhyXMiniProblems/problem_phyx_mini_0802.lean`.**
    Use the stopping-time velocity law to derive upward acceleration
    `2 m/s²`, calculate weight `7840 N`, and solve `T - W = ma` for
    `T = 9440 N`. Finish by simplifying the recorded answer table.

47. **`PhyXMiniProblems/problem_phyx_mini_0803.lean`.**
    Derive the upward `2 m/s²` acceleration from descending-but-slowing
    kinematics, then solve the person’s upward force balance for the `590 N`
    scale reading. Select the physically supported choice A and explicitly
    avoid the inconsistent recorded choice-B metadata.

48. **`PhyXMiniProblems/problem_phyx_mini_0804.lean`.**
    Add the coupled horizontal Newton equations to eliminate internal friction
    and solve for common acceleration `6 m/s²`; then apply the carton equation
    to obtain the tray force `3 N`. Reuse the exact equality to prove the
    displayed choice-B theorem.

49. **`PhyXMiniProblems/problem_phyx_mini_0805.lean`.**
    Solve the two Atwood Newton equations with the common-tension and
    common-acceleration constraints, clearing the positive denominator
    `m₁+m₂`, to obtain `T = m₁m₂g/(m₁+m₂)`. Unfold the four formulas and prove B
    is the unique syntactic/algebraic match.

50. **`PhyXMiniProblems/problem_phyx_mini_0806.lean`.**
    Rewrite centripetal force as `mRω²`, convert the stated angular rate to
    `π/6`, and normalize to `125(π/6)²`. Use certified `pi` bounds to place the
    force within `0.05 N` of `34.3` and compare it strictly with every choice.

51. **`PhyXMiniProblems/problem_phyx_mini_0807.lean`.**
    Resolve tension into vertical and radial balances, eliminate tension to
    derive the tangential-speed square, and combine `vT = 2πr` with the radius
    projection. Cancel positive factors to obtain
    `T = 2π sqrt (L cos β/g)` and unfold choice B.

52. **`PhyXMiniProblems/problem_phyx_mini_0808.lean`.**
    Integrate the constant/average force over the stated collision interval or
    directly rewrite the impulse law, substitute momentum change and duration,
    and normalize the exact result to `2920300/37 N`. Compare this rational
    with all four displayed integers to select `79000 N`.

53. **`PhyXMiniProblems/problem_phyx_mini_0809.lean`.**
    Use quasistatic work–energy balance to equate push work with gravitational
    potential increase, derive the vertical rise `R(1-cos θ₀)` from circle
    geometry, and rewrite weight as `mg`. Prove the coherent-unit, SI, and
    choice-B conjuncts from the same exact identity.

54. **`PhyXMiniProblems/problem_phyx_mini_0810.lean`.**
    Set final kinetic energy to zero in mechanical-energy conservation, cancel
    positive mass, and solve `h = v²/(2g) = 1000/49`. The nearest-tenth
    predicate for `20.4 m` is an exact rational absolute-value inequality.

55. **`PhyXMiniProblems/problem_phyx_mini_0811.lean`.**
    Apply energy conservation over the vertical drop `R` to derive
    `v² = 294/5`, use speed nonnegativity to select `sqrt (294/5)`, and certify
    the `7.67` rounding interval by squaring its positive rational endpoints.
    Check the remaining displayed speeds by finite cases.

56. **`PhyXMiniProblems/problem_phyx_mini_0812.lean`.**
    Rearrange the outbound and return work–energy equations, including friction
    with its correct sign, to obtain return speed square `159/25`. Select the
    positive root and compare its square with midpoint thresholds to prove
    `2.5 m/s` is a closest displayed answer.

57. **`PhyXMiniProblems/problem_phyx_mini_0813.lean`.**
    Rewrite conservation of spring-plus-kinetic energy at the two positions to
    derive velocity square `9/100`. Use the stated return direction to reject
    the positive root and obtain signed velocity `-3/10`, then unfold answer B.

58. **`PhyXMiniProblems/problem_phyx_mini_0814.lean`.**
    Expand the work–energy balance for engine work, gravity, and final spring
    energy, substitute all endpoint readouts, and solve the linear stiffness
    equation for `10600 N/m`. Reuse that equality to close the exact displayed
    choice-B target.

59. **`PhyXMiniProblems/problem_phyx_mini_0815.lean`.**
    From swing energy derive the nonnegative post-impact speed
    `sqrt (2gh)`, then solve horizontal momentum conservation across the
    embedding collision for the bullet’s initial speed and simplify the mass
    ratio. Match the resulting symbolic expression against the finite answer
    formulas.

60. **`PhyXMiniProblems/problem_phyx_mini_0816.lean`.**
    Combine elastic-collision momentum and kinetic-energy conservation with the
    stated components to derive puck B’s final speed square `20`. Select
    `sqrt 20` using nonnegativity and square tight decimal endpoints to prove
    rounding to `4.47` and strict closest-choice inequalities.

61. **`PhyXMiniProblems/problem_phyx_mini_0817.lean`.**
    Expand equality of the initial and final center-of-mass positions and use
    rigid axial displacement definitions to obtain the mass-weighted
    displacement balance. Insert the two masses and partner displacement,
    solve for Ramon’s signed displacement, and simplify its absolute value to
    `9 m` and choice B.

62. **`PhyXMiniProblems/problem_phyx_mini_0818.lean`.**
    Convert `2400 rev/min` to `80π rad/s`, prove the forward and tangential
    tip-velocity components are orthogonal, and obtain the Pythagorean speed
    bound. Solve the admissibility inequality for radius, prove the saturated
    candidate is maximal, and use certified `pi`/square-root bounds for the
    displayed choice.

63. **`PhyXMiniProblems/problem_phyx_mini_0819.lean`.**
    Sum the three point-mass terms to compute `I₁ = 57/1000`, reduce the
    Physlib tensor contraction along axis 1 to `Iω²/2`, and specialize
    `ω = 4` to `57/125 J`. Normalize the decimal display predicate and finish
    its finite answer comparison.

64. **`PhyXMiniProblems/problem_phyx_mini_0820.lean`.**
    Rewrite the `18 J` work balance using uniform-disk inertia and no slip so it
    becomes a scalar equation in cable speed square. Prove the speed is
    nonnegative, select `v = 6/5`, and show choice B is the sole exact match.

65. **`PhyXMiniProblems/problem_phyx_mini_0821.lean`.**
    Compose the cable-length constraints to identify block speed with cylinder
    rim speed, then divide by the strictly positive cylinder radius to obtain
    `ω = v/R`. Rewrite the answer formula for choice B and prove the remaining
    choices differ under the physical positivity assumptions.

66. **`PhyXMiniProblems/problem_phyx_mini_0822.lean`.**
    Specialize the uniform hollow-cylinder inertia law to the symmetry axis and
    simplify the perpendicular-distance integral/tensor formula to
    `(1/2)M(R₁²+R₂²)`. The answer predicate closes by unfolding coefficient B.

67. **`PhyXMiniProblems/problem_phyx_mini_0823.lean`.**
    Evaluate the cross product of the lever arm and force from the figure,
    simplify the signed z-component to `720 cos 19°`, and prove it positive.
    Certify a cosine interval yielding the displayed `680 N m` tolerance and
    the counterclockwise rotation sense.

68. **`PhyXMiniProblems/problem_phyx_mini_0824.lean`.**
    Substitute `I = MR²/2` and `v = Rω` into rolling energy conservation,
    cancel positive mass, and derive `v² = (4/3)gh`. Use speed nonnegativity to
    choose the square root and unfold the coefficient table to identify B.

69. **`PhyXMiniProblems/problem_phyx_mini_0825.lean`.**
    Reduce Physlib’s solid-sphere inertia tensor along the rolling axis to
    `(2/5)MR²`, then eliminate linear/angular acceleration from translation,
    torque, and no-slip equations. Use ramp sign conventions and positivity to
    turn the signed component into friction magnitude `(2/7)Mg sin β`, choice B.

70. **`PhyXMiniProblems/problem_phyx_mini_0826.lean`.**
    Expand torque-free angular-momentum conservation before and after coupling,
    collect the two positive inertias, and divide by their positive sum to get
    the inertia-weighted mean angular velocity. Rewrite choice B’s formula and
    prove its exact match.

71. **`PhyXMiniProblems/problem_phyx_mini_0827.lean`.**
    Compute rod-plus-particle inertia and initial particle angular momentum from
    the supplied geometry, then solve conservation for
    `ω = 800/2001`. Prove the nearest-hundredth and unique-choice predicates by
    rational absolute-error comparisons.

72. **`PhyXMiniProblems/problem_phyx_mini_0828.lean`.**
    Use orthogonality of airspeed and wind to derive ground-speed square
    `500²+50²`, select the positive root `50 sqrt 101`, and bound it strictly
    between the half-integers around `502`. Rewrite Mathlib’s rounding
    characterization and enumerate the displayed choices.

73. **`PhyXMiniProblems/problem_phyx_mini_0829.lean`.**
    Read the two endpoints of student A’s straight trace, prove the elapsed
    time is nonzero, and apply the finite-difference velocity law to obtain
    `2/0.4 = 5 m/s`. Unfold the answer table and prove B is the unique exact
    match.

74. **`PhyXMiniProblems/problem_phyx_mini_0831.lean`.**
    Derive the two source-to-dot distances from the equal-arm geometry, expand
    the two Coulomb field vectors into components, and compute the norm of their
    sum. Bound all radicals/rational denominators tightly enough for the
    `7.64×10³ N/C` display interval and strict closest-choice comparisons.

75. **`PhyXMiniProblems/problem_phyx_mini_0832.lean`.**
    Rewrite each of the three Coulomb contributions using the figure
    coordinates, add components exactly, and square the resultant norm.
    Establish `1.08×10⁵ < ‖E‖ < 1.09×10⁵` by rational radical bounds, then
    compare this interval with every displayed magnitude to select D.

76. **`PhyXMiniProblems/problem_phyx_mini_0833.lean`.**
    Normalize the three point-charge displacement vectors and distances, sum
    their signed Coulomb components, and derive rational upper/lower bounds for
    the resultant norm square. Take the nonnegative root and prove
    `1.34×10⁵ N/C` is uniquely closest among the four choices.

77. **`PhyXMiniProblems/problem_phyx_mini_0834.lean`.**
    First rewrite the physical field as the source-by-source Coulomb sum; then
    specialize the three charges and rectangle coordinates and bound the norm
    between `85.5` and `86.5 kN/C`. Use those strict bounds to establish
    nearest-thousand rounding and all four unique-choice inequalities.

78. **`PhyXMiniProblems/problem_phyx_mini_0835.lean`.**
    Prove integrability on the finite rod, evaluate the axial Coulomb integral
    with an explicit antiderivative, and simplify it to
    `kQ/(r²-(L/2)²)` using the positive separation hypotheses. Substitute the
    calibrated readouts and certify the `9.8×10⁴ N/C` rounding interval.

79. **`PhyXMiniProblems/problem_phyx_mini_0836.lean`.**
    Eliminate flight time from the `45°` equal-height projectile equations to
    obtain `a=v₀²/R`, combine it with `ma=|q|E`, and clear positive charge/range
    denominators. Substitute CODATA rationals and bound the result within
    `50 N/C` of `3.6×10³` before selecting D.

80. **`PhyXMiniProblems/problem_phyx_mini_0837.lean`.**
    Use the limiting nonimpact condition in the vertical trajectory to derive
    `v² = 2(|q|/m)Ed/sin²θ`; prove every division is by a positive quantity.
    Reduce `sin²45°` to `1/2`, normalize to `1.408×10¹⁴`, and square decimal
    endpoints around `1.19×10⁷` for the displayed answer.

81. **`PhyXMiniProblems/problem_phyx_mini_0838.lean`.**
    Solve the uniform-field energy and right-angle boundary equations for
    `E = 2K/(|q|L)`, then model the normal trajectory as a concave quadratic and
    complete the square to show its maximum clearance is `L/4`. Specialize the
    given readouts separately to the field value and the millimetre choice,
    preserving the source’s dimensional distinction.

82. **`PhyXMiniProblems/problem_phyx_mini_0839.lean`.**
    Establish positivity/integrability on the stirrer interval, integrate the
    inverse-distance line-charge force with `log` as antiderivative, and
    simplify endpoint terms to the declared closed form. Prove the sign gives
    “away from wire,” then use certified logarithm bounds for choice-D
    precision.

83. **`PhyXMiniProblems/problem_phyx_mini_0840.lean`.**
    Sum the five outward-normal field components to `5`, multiply by the common
    positive face area, and combine with Gauss’s law and negative enclosed
    charge to make total flux negative. Solve the strict linear inequality for
    the missing component, convert its sign to inward strength, and unfold D.

84. **`PhyXMiniProblems/problem_phyx_mini_0841.lean`.**
    Normalize the five displayed components to an outward sum of `5`, derive
    negative total flux from negative charge and positive permittivity, and
    subtract the known positive contribution. `linarith` then gives the unknown
    back-face component `< -5`, exactly the signed threshold conclusion.

85. **`PhyXMiniProblems/problem_phyx_mini_0842.lean`.**
    Evaluate the shown-face fold/sum to `5`, rewrite Gauss’s law using the
    common positive area, and infer the unshown face contributes less than
    `-5`. Translate that signed result to inward strength `>5` and prove D is
    the unique displayed critical threshold by cases.

86. **`PhyXMiniProblems/problem_phyx_mini_0844.lean`.**
    Use uniformity and the planar flux law to obtain the exact area times
    direction-dot-normal expression, rewrite the figure angle as `120°`, and
    simplify `cos 120° = -1/2` to `-81/40`. The one-decimal match and uniqueness
    are rational computations.

87. **`PhyXMiniProblems/problem_phyx_mini_0845.lean`.**
    Rearrange the planar uniform-field flux law using positive area and
    nonzero projected cosine, then specialize the rectangle and `60°` geometry
    to `2500/sqrt 3`. Prove `sqrt 3 > 0` and certify rational radical bounds
    tight enough for the displayed field-strength choice.

88. **`PhyXMiniProblems/problem_phyx_mini_0847.lean`.**
    Evaluate the torus enclosure predicate to net charge `-1 nC`, substitute it
    into Gauss’s law with the stated rational permittivity, and normalize the
    flux to `-20000/177`. Compare this exact rational with all displayed fluxes
    to show `-110` is uniquely closest.

89. **`PhyXMiniProblems/problem_phyx_mini_0848.lean`.**
    Prove only the central `+1 nC` source belongs to the Gaussian cylinder,
    rewrite Gauss’s law as flux equals charge over positive permittivity, and
    normalize to `10^13/88541878128`. Cross-multiply positive denominators to
    show `110 N m²/C` minimizes the displayed error.

90. **`PhyXMiniProblems/problem_phyx_mini_0849.lean`.**
    Evaluate the exterior sheet/conductor law as `ne/ε₀`, cross-multiply the
    positive permittivity calibration to prove the `900 N/C` rounding bounds,
    and use the conductor/cavity laws to set points 2 and 3 to zero. Unfold the
    answer table to prove D uniquely matches the nonzero point-1 field.

91. **`PhyXMiniProblems/problem_phyx_mini_0850.lean`.**
    Pair faces 1/3 and 2/4, rewrite opposite outward normals as negatives, and
    use uniformity plus bilinearity of the dot product to cancel each pair’s
    flux. Sum to zero and close the choice-D predicate from the independent
    physical equality.

92. **`PhyXMiniProblems/problem_phyx_mini_0851.lean`.**
    Use the figure geometry to place the axial field vector in surface 3’s
    tangent plane, apply tangent-normal orthogonality to make its dot product
    with the area vector zero, and rewrite the planar flux law. Substitute the
    zero result into the displayed table to identify D.

93. **`PhyXMiniProblems/problem_phyx_mini_0852.lean`.**
    Apply Gauss’s law to a surface inside the conductor to prove inner charge
    cancels the central charge; apply it to the positive-radius cavity sample
    to derive positivity of the central charge. Combine both balances to obtain
    the exact negative inner-surface expression and prove it differs from
    recorded zero metadata.

94. **`PhyXMiniProblems/problem_phyx_mini_0853.lean`.**
    Rewrite conservation of electrostatic plus kinetic energy across the
    one-millimetre motion, substitute electron mass/charge and field readouts,
    and derive an exact squared-speed interval. Use nonnegative speed and
    squared midpoint bounds to show `1000 m/s` is uniquely closest.

95. **`PhyXMiniProblems/problem_phyx_mini_0854.lean`.**
    Derive both electron–proton distances from the figure, substitute them into
    the signed pairwise Coulomb-potential sum, and simplify powers of ten and
    elementary charges before rounding. Establish a certified interval around
    the physically corrected `10^-19 J` choice and enumerate alternatives.

96. **`PhyXMiniProblems/problem_phyx_mini_0855.lean`.**
    Prove the `3-4-5` diagonal by squaring positive lengths, normalize the three
    pairwise charge-over-distance terms to `53/10^17`, and multiply by the
    calibrated Coulomb constant. Use exact rational arithmetic to close the
    energy result and its literal answer-table relation.

97. **`PhyXMiniProblems/problem_phyx_mini_0857.lean`.**
    Convert point C’s `2 cm` radius to metres, specialize the point-charge
    potential law, and substitute `k=9×10^9` and `q=2 nC`. `norm_num` reduces
    the expression to exactly `900 V`, after which the displayed choice follows.

98. **`PhyXMiniProblems/problem_phyx_mini_0858.lean`.**
    Use the `3-4-5` rectangle to rewrite all source distances, specialize
    point-charge potential and scalar superposition, and normalize the resulting
    Coulomb sum. Bound it within `50 V` of `1800 V`, then prove D’s error is
    strictly smaller than every alternative.

99. **`PhyXMiniProblems/problem_phyx_mini_0859.lean`.**
    Prove the equilateral centroid distance `s/sqrt 3`, rewrite the three signed
    source potentials over that common distance, and simplify their charge sum.
    Use positive `sqrt 3` plus rational bounds to establish
    `-1650 < V < -1550`, then select the unique displayed voltage.

100. **`PhyXMiniProblems/problem_phyx_mini_0860.lean`.**
    Derive the three distances `2sqrt 5`, `4`, and `2 cm`, substitute them into
    the superposed point-charge potential, and isolate the unknown charge.
    Translate the rounded `3140 V` readout into an interval, use `sqrt 5` bounds
    to show only the `10 nC` candidate lies in it, and prove choice D unique.

101. **`PhyXMiniProblems/problem_phyx_mini_0861.lean`.**
    Evaluate the two-source Coulomb field at a reflected pair of exterior
    samples, rewrite midpoint reflection distances, and clear their nonzero
    denominators to derive `q₁+q₂=0`. Use nonzero charges to simplify absolute
    values and obtain magnitude ratio `1`, then unfold choice D.

102. **`PhyXMiniProblems/problem_phyx_mini_0862.lean`.**
    First prove the Physlib axial profile equals
    `kq(x-x₀)/|x-x₀|³`; specialize it at the two reflected exterior samples and
    use their equal-height image readout. Rewrite reflected distances, clear
    positive/nonzero denominators, solve the resulting linear charge relation,
    and finish the requested magnitude ratio.

103. **`PhyXMiniProblems/problem_phyx_mini_0863.lean`.**
    Prove distance invariance under reflection `x ↦ -x`, use opposite half-rod
    charge densities to show paired potential contributions cancel, and apply
    interval-integral reflection/substitution to make the total potential zero.
    Unfold the displayed voltages and prove the zero choice unique.

104. **`PhyXMiniProblems/problem_phyx_mini_0864.lean`.**
    Establish the four edge and two diagonal separations of the initial square,
    sum all six Coulomb pair energies, and equate that energy with four equal
    final kinetic energies at infinite separation. Cancel positive mass, select
    the common nonnegative speed root, and certify its displayed rounding.

105. **`PhyXMiniProblems/problem_phyx_mini_0865.lean`.**
    Apply `K+qV` conservation between the two diagram points, substitute the
    standard positive proton charge/mass and potential readouts, and solve for
    speed square. Select the nonnegative root and compare squared midpoints to
    prove `1×10^5 m/s` (D) is uniquely nearest.

106. **`PhyXMiniProblems/problem_phyx_mini_0866.lean`.**
    Derive midpoint potential `250 V` and collision-plate potential `0 V` from
    the uniform-potential law, then rearrange proton energy conservation to an
    exact collision-speed square. Use positive-root selection and integer
    squared bounds to place the speed within `500 m/s` of `296000`, and finish
    choice D.

107. **`PhyXMiniProblems/problem_phyx_mini_0867.lean`.**
    Compute both facing-point distances, expand the two sphere-potential sums,
    and subtract them with the stated charge/radius readouts. Bound the remaining
    rational/radical expression in the `2100 V` rounding interval, prove its
    sign is positive, and compare all displayed choices.

108. **`PhyXMiniProblems/problem_phyx_mini_0868.lean`.**
    Evaluate the supplied piecewise electric-field graph integral from `1` to
    `3` by splitting at its breakpoint and using the constant/linear segment
    formulas. Apply `ΔV = -∫E·dx` to obtain `-200 V`, then unfold the answer
    table and show D is the unique exact match.

109. **`PhyXMiniProblems/problem_phyx_mini_0869.lean`.**
    Compute the signed graph area from `0` to `3` as `150 V`, combine
    `V(0) = -50 V` with `V(3)-V(0) = -150 V`, and derive `V(3)=-200 V`.
    Rewrite the displayed values and prove choice D uniquely matches.

110. **`PhyXMiniProblems/problem_phyx_mini_0870.lean`.**
    Convert the perpendicular `1 cm` equipotential spacing to `0.01 m`, divide
    the `200 V` drop by that positive distance, and derive
    `20000 V/m = 20 kV/m`. Rewrite the answer units and prove D is the unique
    exact match.

111. **`PhyXMiniProblems/problem_phyx_mini_0871.lean`.**
    Apply the adjacent-equipotential gradient law at the marked dot, normalize
    `200 V / 1 cm` to `20 kV/m`, and use positivity to remove any magnitude
    absolute value. Unfold the finite answer table to prove D’s exact match and
    uniqueness.

112. **`PhyXMiniProblems/problem_phyx_mini_0872.lean`.**
    Rearrange the oriented Kirchhoff loop equation to isolate `ΔV₃₄`, substitute
    the other three directed changes, and reduce to `-20 V` by `linarith` and
    `norm_num`. Enumerate the displayed values to prove D is the sole match.

113. **`PhyXMiniProblems/problem_phyx_mini_0873.lean`.**
    Rearrange `|Q| = CΔV` using the strictly positive potential difference,
    substitute `20 nC` and `100 V`, and normalize unit conversions to
    `1/5 nF`. Reuse the exact capacitance equality to close answer D.

114. **`PhyXMiniProblems/problem_phyx_mini_0874.lean`.**
    Prove the centimetre/metre readout conversion from PhysLean’s unit scaling,
    then apply the uniform static-field potential law to the A-to-B displacement.
    The vertical `3 cm` offset has zero dot product with the horizontal field;
    the horizontal `7 cm` component gives `V(B)-V(A)=-70 V`, matching D.

115. **`PhyXMiniProblems/problem_phyx_mini_0875.lean`.**
    Normalize the literal query coordinate to both `2 cm` and `0.02 m`, select
    the middle piece of the potential profile, and differentiate `V(x)=10x`.
    Apply `E_x=-dV/dx` to obtain `-10 V/m`, then evaluate all four choices to
    prove the physically supported value matches none of them.

116. **`PhyXMiniProblems/problem_phyx_mini_0876.lean`.**
    Derive the centered probe separation `2 cm` and contour span `75 V`, apply
    the centered finite-difference field-magnitude law, and convert the
    denominator to `0.02 m`. Normalize to `3750 V/m` and close the recorded
    choice-D predicate by exact arithmetic.

117. **`PhyXMiniProblems/problem_phyx_mini_0877.lean`.**
    Use the parallel-capacitance law for the lower branch to obtain `30 μF`,
    then apply the two-capacitor series reciprocal/product-over-sum formula with
    the top `10 μF`. Positivity justifies the denominators; normalization gives
    `7.5 μF`, exactly choice D.

118. **`PhyXMiniProblems/problem_phyx_mini_0878.lean`.**
    Combine the two center capacitors in series to `12 μF`, add the remaining
    parallel capacitance to obtain `25 μF`, and use those helper equalities to
    close the network theorem. Unfold the four displayed capacitances to prove
    D is the unique recorded match.

119. **`PhyXMiniProblems/problem_phyx_mini_0879.lean`.**
    Use neutrality at both floating junctions and opposite plate signs to prove
    all three series charge magnitudes equal. Substitute `ΔVᵢ=Q/Cᵢ` into KVL,
    clear the positive capacitance product, and solve for `Q=60 μC`; finish
    exact match and uniqueness by cases.

120. **`PhyXMiniProblems/problem_phyx_mini_0880.lean`.**
    Add the `4 μF` and `12 μF` parallel capacitances to `16 μF`, reduce the
    remaining series/voltage-division circuit equations with positive
    denominators, and solve for charge on `C₃` as `16 μC`. Rewrite the displayed
    table to close choice D.

121. **`PhyXMiniProblems/problem_phyx_mini_0881.lean`.**
    Rewrite the long-time ideal-inductor voltage as zero, apply Ohm’s law to
    each `20 Ω` branch to obtain `0.5 A`, and use junction current conservation
    to add them to `1 A`. Prove choice C is the unique exact battery-current
    match.

122. **`PhyXMiniProblems/problem_phyx_mini_0883.lean`.**
    Express motional emf as the line integral of `v×B` along the bar, substitute
    the long-wire field `μI/(2πr)`, and integrate `1/r` from `d` to `d+l`.
    Positivity of `d,l,μ,v,I` fixes the near-minus-far sign and yields the
    logarithmic formula printed as choice C.

123. **`PhyXMiniProblems/problem_phyx_mini_0884.lean`.**
    Use square geometry to compute the initial and collapsed diagonals as
    `sqrt 2*s` and `2s`, divide their difference by the positive relative speed
    `2v`, and substitute `s=0.10`, `v=0.293`. Bound `sqrt 2` rationally to prove
    the exact duration rounds to `0.1 s` and choice C.

124. **`PhyXMiniProblems/problem_phyx_mini_0885.lean`.**
    Substitute `r₂/r₁=6` and the calibrated permeability into the coaxial
    inductance-per-length law, justify the positive logarithm argument, and
    certify a tight bound for `log 6`. Convert henries/metre to microhenries/metre
    and prove `0.36` is the unique two-decimal match.

125. **`PhyXMiniProblems/problem_phyx_mini_0886.lean`.**
    Resolve the second-quadrant figure geometry to phase `5π/6` modulo a full
    turn, use periodicity and `cos (5π/6)=-sqrt 3/2`, and simplify the exact
    projection to `-6sqrt 3`. Rational `sqrt 3` bounds prove `-10 V` is uniquely
    nearest among the integer choices.

126. **`PhyXMiniProblems/problem_phyx_mini_0887.lean`.**
    Rewrite capacitive reactance as `1/(2πfC)` and the series-RC capacitor
    amplitude via impedance magnitude, proving all denominators positive.
    Substitute `10 kHz`, `80 nF`, `150 Ω`, and the source amplitude; use
    certified `pi` and square-root bounds to establish the `8.0 V` display.

127. **`PhyXMiniProblems/problem_phyx_mini_0888.lean`.**
    Derive `V_R(ω)=E₀R/sqrt(R²+(ωL)²)` from the series-RL impedance law, then
    prove the denominator tends to positive `R` as `ω→0+` using continuity of
    square, addition, and square root. Simplify the limit with `R>0` to `E₀`
    and unfold choice C.

128. **`PhyXMiniProblems/problem_phyx_mini_0889.lean`.**
    Specialize the ideal resonance law to `L=10^-3` and `C=10^-6`, reduce the
    positive square root of their product, and retain the exact
    `1/(2πsqrt(LC))` frequency. Use certified `pi` bounds to place it near
    `5033 Hz` and prove `5.0×10³ Hz` is uniquely closest.
