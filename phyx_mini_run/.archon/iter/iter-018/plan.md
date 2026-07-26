# Iteration 018 Plan

## Batch contract

- Preserve exactly the 128 loop-selected Current Objectives below, in their
  existing order: six mandatory proof-Review retries followed by 122 new
  accepted-open targets. No `proof_review_exhausted` target is present.
- Eligibility shortfall: 0. The fixed list exceeds the desired
  `max_parallel = 32` occupancy by 96 targets; execution should keep 32
  distinct lanes occupied while draining this ordered list, dispatching the
  six retries first. Plan does not truncate or otherwise mutate the list.
- Preserve every theorem statement and physical hypothesis. Derive exact
  physical relations before finite-precision answer predicates, establish all
  denominator/branch signs explicitly, and certify radical, exponential,
  trigonometric, inverse-trigonometric, `pi`, and rounding bounds.
- The supplied blueprint excerpts expose no chapter-level mismatch requiring
  correction, so no blueprint chapter is edited. In `0546`, the auxiliary
  regularization lemma's `ContinuousAt` hypothesis does not supply the
  measurability needed for its Bochner integrals; keep that irreducible gap
  honest if no theorem under the frozen statement closes it.

## Per-target proof strategy

1. **`PhyXMiniProblems/problem_phyx_mini_0428.lean` (retry; 2/3 used).**
   Re-elaborate the existing thermodynamic derivation: certify the cube identity
   and rational bounds for `6^(2/3)`, use the heat signs to simplify both
   `max` terms, cancel the positive `nR` factors, and finish the displayed
   efficiency interval from reciprocal bounds.

2. **`PhyXMiniProblems/problem_phyx_mini_0439.lean` (retry; 2/3 used).**
   Normalize all mass, volume, and specific-volume readouts to SI; derive
   tank A's mass as `2`, substitute tank B's mass into its volume law, then use
   rigid total-volume, mass-conservation, and final-state laws in a typed
   `calc`/`linarith` chain to obtain `(2 + 7 v_B)/11`.

3. **`PhyXMiniProblems/problem_phyx_mini_0544.lean` (retry; 1/3 used).**
   Rebuild the boundary-matching algebra without fragile rewriting: solve the
   two continuity equations for the transmitted-amplitude ratio, prove every
   wave-number and square-root denominator positive from `E > V₀`, substitute
   the dispersion laws, and normalize the requested coefficient and choice-D
   conjuncts.

4. **`PhyXMiniProblems/problem_phyx_mini_0546.lean` (retry; 1/3 used).**
   Close the ground-state center-density and first-order energy target by
   rewriting the sine profile at `L/2`, using positivity of `L`, and applying
   the stated Dirac perturbation law. For the separate rectangular-limit
   lemma, search only for a theorem that derives the required local integral
   limit under exactly `ContinuousAt`; otherwise retain its clearly marked
   `sorry`, since arbitrary point-continuous functions need not be strongly
   measurable.

5. **`PhyXMiniProblems/problem_phyx_mini_0583.lean` (retry; 1/3 used).**
   Retain the exact probability reduction and replace any brittle numeric
   closure with named rational bounds for `pi`, `sin (pi/30)`, and
   `cos (2*pi/5)`; propagate positivity through `gcongr`, trap the product in
   the required rounding interval, and unfold the answer predicate once.

6. **`PhyXMiniProblems/problem_phyx_mini_0606.lean` (retry; 1/3 used).**
   Keep the explicit diagonal Hamiltonian proof: separate the ground and
   excited eigenvalues using positive `Jℏ²`, characterize the ground
   eigenspace coefficientwise in the chosen basis, identify it with the span
   of the four zero-index vectors, and compute finrank/cardinality before the
   answer readout.

7. **`PhyXMiniProblems/problem_phyx_mini_0625.lean`.**
   Apply the finite-graph handshaking theorem to six-regularity, rewrite the
   degree sum as `6 * card Atom`, and cancel the factor two to get
   `edgeFinset.card = 3 * card Atom`; cast this identity into the fusion balance,
   cancel the positive atom count, and normalize the calibrated value and
   unique closest choice.

8. **`PhyXMiniProblems/problem_phyx_mini_0626.lean`.**
   Rewrite the Hall, atomic-density, carrier-balance, measurement, and reference
   fields into one rational expression for carriers per atom; discharge
   nonzero denominators from physical positivity, then enumerate the four
   choices and solve the absolute-value closeness and half-step rounding bounds
   by exact arithmetic.

9. **`PhyXMiniProblems/problem_phyx_mini_0628.lean`.**
   Eliminate the `l=1` and `l=0` rotor energies with the photon relation to
   derive `λ = 2πIc/ℏ`, proving `ℏ ≠ 0`; then substitute the calibrated
   constants, prove a certified interval around `2.58817 mm`, and enumerate
   choices to establish the `2.59 mm` tolerance and uniqueness.

10. **`PhyXMiniProblems/problem_phyx_mini_0630.lean`.**
    Rewrite the acceptor/donor densities and n-side depth in charge neutrality,
    cancel the positive conversion factors, and solve `N_A a_p = N_D a_n` for
    `a_p = 275 nm`; unfold the four displayed depths and finish the match and
    iff uniqueness by cases.

11. **`PhyXMiniProblems/problem_phyx_mini_0631.lean`.**
    Use the ordered, distinct, complete lowest-transition hypotheses plus
    `Δl = ±1` to identify the long-wavelength band as `1→0`; independently
    rewrite `Eλ = hc` at `4.2972 μm`, bound the calibrated quotient within
    `10⁻⁵ eV`, enumerate competing choices, and assemble the target from the
    two helpers.

12. **`PhyXMiniProblems/problem_phyx_mini_0632.lean`.**
    Substitute the four-year duration and constant radial expansion into the
    spherical arc law to obtain the exact `(500 + 10⁻⁶ t)π/3` readout; use
    certified rational bounds on `pi` to place it in `[655.5,656.5)`, then
    unfold and case-split the unique answer predicate.

13. **`PhyXMiniProblems/problem_phyx_mini_0633.lean`.**
    Evaluate the one-dimensional Lorentz boost at the two simultaneous events,
    simplify `γ(4/5)` to `5/3` using the positive square-root branch, and use
    the opposite `±300 m` coordinates to obtain equal and opposite Peggy
    times; certify the displayed microsecond rounding in the main theorem.

14. **`PhyXMiniProblems/problem_phyx_mini_0634.lean`.**
    Derive the circular radius by expanding the chord/sagitta equation and
    dividing by the positive deflection; eliminate speed between magnetic
    circular motion, Lorentz balance, and the plate-field law, substitute all
    readouts, and prove the resulting voltage's closest displayed choice by
    finite cases.

15. **`PhyXMiniProblems/problem_phyx_mini_0635.lean`.**
    Prove the elementary-charge conversion by unfolding the unit readouts;
    combine zero final kinetic energy, zero initial potential, Coulomb
    potential, and mechanical-energy conservation to solve for closest
    approach, then substitute charge/mass/speed calibrations and certify the
    numerical answer interval and unique choice.

16. **`PhyXMiniProblems/problem_phyx_mini_0636.lean`.**
    First derive the signed Coulomb energy balance from conservation, then
    rewrite the cesium/beta charges, radius, final `300 keV`, and joule/MeV
    conversions to the positive correction formula; bound the physical
    constants tightly enough for the ejection-energy display and uniqueness
    predicates.

17. **`PhyXMiniProblems/problem_phyx_mini_0637.lean`.**
    Expand the unique-closest absorbed-level predicate and exclude all
    principal numbers except `5` using the hydrogen spectrum and rounded
    absorption interval; combine `Δn=3` to get `5→2`, solve the photon law for
    wavelength with a positive gap, and certify the final displayed choice.

18. **`PhyXMiniProblems/problem_phyx_mini_0638.lean`.**
    Normalize and integrate the exponential density to obtain the exact tail
    `exp(-2)`, use the counting law for `10⁶ exp(-2)`, and prove a sufficiently
    sharp certified exponential interval—via the imported series/remainder
    bounds—to place the count in `[135334.5,135335.5)`.

19. **`PhyXMiniProblems/problem_phyx_mini_0639.lean`.**
    Rewrite `E=ΔV/d` to get `25000 V/m`, use the positive speed in the
    undeflected Lorentz balance to solve `B=E/v=0.005 T`, convert teslas to
    milliteslas, and close the recorded-choice conjunction by definitional
    simplification.

20. **`PhyXMiniProblems/problem_phyx_mini_0640.lean`.**
    Derive `E=50000 V/m`; eliminate transit time and electric deflection to
    obtain the positive speed, use force balance for the square-root magnetic
    field formula, and certify the radical between rational endpoints that
    imply the whole-millitesla rounding and unique closest answer.

21. **`PhyXMiniProblems/problem_phyx_mini_0641.lean`.**
    Resolve the scattering directions into two planar momentum components,
    substitute the mass-number ratio and initially stationary gold momentum,
    square and add to isolate recoil speed, then use rational square bounds to
    prove the `252000 ± 500 m/s` interval and enumerate unique closeness.

22. **`PhyXMiniProblems/problem_phyx_mini_0643.lean`.**
    Derive the calibrated fringe spacing `925/14 μm`, substitute it into
    `Δy=λL/d` to get `185/98 fm`, and solve de Broglie for speed after proving
    mass/wavelength positivity; bound the exact constant expression, show its
    one-significant-figure result, and prove that none of the inconsistent
    displayed speeds matches where required.

23. **`PhyXMiniProblems/problem_phyx_mini_0644.lean`.**
    Rewrite the ground and continuum energy readouts in the ionization law,
    use `linarith` to obtain `13/2 eV`, then unfold the displayed energies and
    discharge choice B's match and uniqueness by four finite cases.

24. **`PhyXMiniProblems/problem_phyx_mini_0645.lean`.**
    Use normalization of the triangular density to determine its peak, evaluate
    the affine right-branch integral on the `0.010 mm` strip as `1/900`, apply
    the million-trial expectation law to get `10000/9`, and decide strict
    closeness against all four integer displays.

25. **`PhyXMiniProblems/problem_phyx_mini_0646.lean`.**
    Apply `c=λν` to both positive peak frequencies and cancel their common
    equal frequency to equate wavelengths; substitute this into Wien's law,
    solve the calibrated product for temperature, and use certified division
    bounds to prove its rounded displayed choice.

26. **`PhyXMiniProblems/problem_phyx_mini_0647.lean`.**
    Rewrite the piecewise wavefunction and normalization law, split the queried
    interval at its breakpoints, evaluate the squared-amplitude integrals
    exactly to `4/5`, and finish the target by unfolding choice B's displayed
    probability.

27. **`PhyXMiniProblems/problem_phyx_mini_0648.lean`.**
    Use the constant-density plateau and normalized `8 mm` support to reduce the
    central `2 mm` interval integral to a length ratio `2/8=1/4`; reuse that
    theorem and unfold the answer table to prove the recorded-choice corollary.

28. **`PhyXMiniProblems/problem_phyx_mini_0649.lean`.**
    Combine `T=2Δt`, `rate=1/T`, and `bandwidth=1/Δt`, canceling only positive
    durations, to prove the unit-generic half-bandwidth relation; specialize to
    `200 kHz`, convert to `100000 s⁻¹`, and simplify the choice-C predicate.

29. **`PhyXMiniProblems/problem_phyx_mini_0650.lean`.**
    Decompose the apparent rod into longitudinal and transverse components,
    restore only the longitudinal component with `γ(0.995)`, and use the
    Pythagorean law for proper length; certify square-root and gamma bounds
    placing the result within `0.05 m` of `17.4`.

30. **`PhyXMiniProblems/problem_phyx_mini_0651.lean`.**
    Integrate the two triangular branches in the normalization equation to get
    peak amplitude squared `3`; integrate the first-quarter branch to `1/36`,
    then prove thousandth rounding and strict closest-choice inequalities by
    exact rational arithmetic.

31. **`PhyXMiniProblems/problem_phyx_mini_0652.lean`.**
    Rewrite the normalized linear wavefunction on `[-4,4]`, evaluate its
    squared integral on the central `[-2,2]` interval, cancel the normalization
    constant to obtain `1/8`, and reuse the helper to prove the recorded
    choice's exact match and uniqueness.

32. **`PhyXMiniProblems/problem_phyx_mini_0653.lean`.**
    Unfold the supplied positive symmetric triangular profile, show every
    coordinate's density is bounded by its apex value with equality only at
    zero, package this as the unique-most-likely predicate, and case-split the
    displayed coordinates to isolate choice C.

33. **`PhyXMiniProblems/problem_phyx_mini_0654.lean`.**
    Eliminate momentum, kinetic energy, and the escape boundary to derive
    `h=ℏ²/(8m²gw²)` with all factors positive; substitute literal calibrations,
    bound the quotient in `[1.41,1.42]·10⁻²⁸`, and compare that supported value
    against every displayed depth to prove A—not the recorded metadata—is
    uniquely nearest.

34. **`PhyXMiniProblems/problem_phyx_mini_0655.lean`.**
    Obtain the paraxial-remainder inequality directly from the response law,
    then combine it with de Broglie wavelength, free-fall speed, and the
    diameter readout; clear positive denominators and propagate certified
    constant bounds to trap the exact distance in `(4.3,4.5)·10¹¹ m`, which
    makes C uniquely closest.

35. **`PhyXMiniProblems/problem_phyx_mini_0656.lean`.**
    Read four lobes through the general mode/lobe law to get `n=4`; substitute
    the energy and electron-mass calibrations into the rigid-box spectrum,
    square after proving length positivity, and bound the resulting radical
    within `0.01 nm` of one before simplifying `round (10L)` and choice
    uniqueness.

36. **`PhyXMiniProblems/problem_phyx_mini_0657.lean`.**
    Combine the figure's three lobes/two nodes with both nodal-law fields to
    prove `n=3`; specialize quadratic energy scaling at `n=3`, rewrite the
    `12 eV` readout, solve the ground energy as `4/3 eV`, and discharge the
    displayed-answer conjuncts by finite cases.

37. **`PhyXMiniProblems/problem_phyx_mini_0658.lean`.**
    Algebraically differentiate the symmetric two-neighbor Coulomb force at
    equilibrium to obtain `k=4k_e q²/a³`; identify the Physlib oscillator's
    mass and frequency, compare the supplied Schrödinger equation with the
    nonzero eigenfunction equation, derive the four energy readouts, and
    certify their order and choice-C tolerance.

38. **`PhyXMiniProblems/problem_phyx_mini_0659.lean`.**
    Enumerate the supplied energy-level pairs and use the rounded `492 nm`
    photon relation to isolate `6s8s→6s6p`; rewrite threshold conservation as
    the ground-to-`6s8s` gap, solve `½mv²=ΔE` on the positive-speed branch, and
    certify the displayed minimum-speed choice.

39. **`PhyXMiniProblems/problem_phyx_mini_0660.lean`.**
    Rewrite the literal barrier and alpha energies for the exact `25 MeV`
    difference, substitute the rectangular-barrier transmission law and
    calibrated constants, and use certified square-root/exponential bounds to
    prove the `9.9·10⁻³⁹` display interval; enumerate all four source choices
    to show none matches.

40. **`PhyXMiniProblems/problem_phyx_mini_0661.lean`.**
    Substitute the two pressures and convert `11 cm²` to SI in the statics law
    to obtain exactly `3498/5 N`; unfold nearest-newton and answer-table
    definitions, normalize absolute values, and prove D's rounding, nearest
    status, and uniqueness by cases.

41. **`PhyXMiniProblems/problem_phyx_mini_0662.lean`.**
    Use incipient vertical force balance to derive the `mg/A=98 kPa` gauge
    increment, add the `100 kPa` ambient pressure for `198 kPa` absolute, and
    unfold the displayed-pressure selector to close choice D.

42. **`PhyXMiniProblems/problem_phyx_mini_0664.lean`.**
    Derive `V=Ad=30 m³`, equate buoyancy and total weight and cancel positive
    gravity to get total supported mass `997·30=29910 kg`, then subtract the
    tank's `10000 kg` mass to obtain `19910 kg` and simplify choice D.

43. **`PhyXMiniProblems/problem_phyx_mini_0665.lean`.**
    Combine admissible column geometry with hydrostatic pressure from the open
    surface to the piston, then use the thin-piston force balance to rewrite
    the same pressure in every requested unit system; instantiate the explicit
    formula to prove answer D without assuming a solved elevation.

44. **`PhyXMiniProblems/problem_phyx_mini_0666.lean`.**
    Use meridian right-triangle geometry to express slant height as
    `sqrt(h²+(R-r)²)`, substitute it into the curved-area law
    `π(R+r)s`, and prove the answer iff by cases, canceling positive `pi` and
    radii where alternatives must be excluded.

45. **`PhyXMiniProblems/problem_phyx_mini_0667.lean`.**
    Divide the arc-length law by the nonzero central angle to get `r=d/θ`,
    convert `35°` to radians and simplify to `4320/π`; use rational `pi`
    bounds to place this within five metres of `1380` and outside the other
    ten-metre displays.

46. **`PhyXMiniProblems/problem_phyx_mini_0668.lean`.**
    Telescope the six drop release times to five equal intervals, derive the
    endpoint car displacement from the printed span, substitute both into the
    average-speed law, and normalize the stated span/interval readouts to
    exactly `24 m/s`.

47. **`PhyXMiniProblems/problem_phyx_mini_0670.lean`.**
    Integrate each constant acceleration segment from the initial-rest
    condition to obtain the three velocity pieces, prove the last remains
    nonnegative, and integrate speed over `[0,10]`, `[10,15]`, and `[15,20]`
    to `100+100+125/2=525/2`.

48. **`PhyXMiniProblems/problem_phyx_mini_0671.lean`.**
    Evaluate the signed areas under the piecewise velocity graph through
    `9 s` as `12+16+0=28`, combine with the initial-origin hypothesis, and
    unfold the four displayed positions to prove choice C's equality and iff
    uniqueness.

49. **`PhyXMiniProblems/problem_phyx_mini_0672.lean`.**
    Split the total-distance law at all velocity sign changes and compute the
    four absolute graph areas `48`, `39`, `72`, and `45`; sum them to `204`
    and decide exact matching and uniqueness against the displayed table.

50. **`PhyXMiniProblems/problem_phyx_mini_0673.lean`.**
    Expand squared Euclidean distance to obtain `x²+y²=L²`, differentiate it
    with the two `HasDerivAt` hypotheses to get `x x'+y y'=0`, substitute the
    signed velocity conventions and figure ratios, then rewrite `x/y` as
    `1/tan θ` on the stated acute branch.

51. **`PhyXMiniProblems/problem_phyx_mini_0674.lean`.**
    Apply constant-acceleration displacement over the `3.1 s` crossing to
    solve the entry speed, use the future zero-velocity event to eliminate
    stopping time and derive `v²/(2a)`, then bound the exact rational result
    for the displayed stopping-distance choice.

52. **`PhyXMiniProblems/problem_phyx_mini_0675.lean`.**
    Substitute tangential acceleration `g sin θ` into
    `L=½at²` to derive the time-square formula; prove its right side
    nonnegative and the modeled time positive, then apply square-root
    uniqueness to select `sqrt(2L/(g sin θ))`.

53. **`PhyXMiniProblems/problem_phyx_mini_0676.lean`.**
    Solve the right-triangle tangent law as `width=100 tan 35°`, using
    positivity of the acute-angle tangent, then certify a tight trigonometric
    interval placing the width within `0.05 m` of `70.0` and strictly farther
    from every alternative.

54. **`PhyXMiniProblems/problem_phyx_mini_0677.lean`.**
    Resolve both forces into Cartesian components from their stated polar
    angles, add them using superposition, and prove the squared norm is `91`;
    select the nonnegative square root and bound `sqrt 91` in the one-decimal
    interval for `9.5 N`.

55. **`PhyXMiniProblems/problem_phyx_mini_0678.lean`.**
    Use the figure's angle addition to show the arrow-normal angle is `51°`,
    evaluate the normal projection as `1.5 cos 51°`, and certify cosine bounds
    tight enough for the printed perpendicular-component choice and its
    uniqueness.

56. **`PhyXMiniProblems/problem_phyx_mini_0679.lean`.**
    Subtract the two supplied uniform-motion position equations to solve the
    horizontal velocity as `268 m/s`, advance another `15 s` to horizontal
    coordinate `12060 m`, retain the fixed `7600 m` altitude, and assemble the
    final vector/readout target.

57. **`PhyXMiniProblems/problem_phyx_mini_0680.lean`.**
    Obtain the missing straight side from the figure readouts, apply the cosine
    rule to the `105°` included angle for the direct chord, equate the two race
    times, and certify the resulting radical/cosine quotient within the
    choice-C speed tolerance while excluding other choices.

58. **`PhyXMiniProblems/problem_phyx_mini_0681.lean`.**
    Express static balance as the spider load being the negative sum of the two
    perpendicular tensions, take squared norms, eliminate the cross term by
    orthogonality, and substitute the tension readouts; use the positive force
    branch and radical bounds to finish the displayed load choice.

59. **`PhyXMiniProblems/problem_phyx_mini_0682.lean`.**
    Expand the base diagonal in the `i,j` basis, extend through the orthogonal
    `c` edge using the body right-triangle law, and prove componentwise in the
    requested unit system that `R₂=a i+b j+c k`; unfold choice C afterward.

60. **`PhyXMiniProblems/problem_phyx_mini_0683.lean`.**
    Solve horizontal projectile motion for positive flight time using
    `x=v cos θ·t`, substitute it into vertical motion, and clear the positive
    `v` and acute-angle cosine denominators to obtain the stated trajectory
    height formula.

61. **`PhyXMiniProblems/problem_phyx_mini_0684.lean`.**
    Eliminate actual/model fall times from the horizontal waterfall kinematics
    and geometric scale relations to prove Froude scaling
    `v_m=v_a sqrt λ`; specialize `λ=1/12`, bound the radical product near
    `0.49075`, and close the `0.491` rounding predicate.

62. **`PhyXMiniProblems/problem_phyx_mini_0685.lean`.**
    Eliminate launch speed from the first roof crossing and choose the later
    positive intersection using the physical branch hypothesis; rewrite the
    landing distance as the supplied closed expression, then certify its
    interval around `2.7912 m` for the centimetre display and unique choice C.

63. **`PhyXMiniProblems/problem_phyx_mini_0686.lean`.**
    Use horizontal-speed constancy and vertical energy/kinematics to prove
    `v_impact=sqrt(18²+2·9.8·50)` on the nonnegative branch; bound its square
    between rational squares around `36.11`, and decide the `36.1` tolerance
    and strict closest-choice inequalities.

64. **`PhyXMiniProblems/problem_phyx_mini_0687.lean`.**
    Prove the feet/metres and revolutions-per-minute/second lemmas by unfolding
    the unit scales; substitute radius and centripetal-acceleration readouts to
    solve the positive rotation frequency, convert to rpm, and certify the
    displayed answer by radical bounds.

65. **`PhyXMiniProblems/problem_phyx_mini_0688.lean`.**
    Project the total acceleration onto the tangential direction using the
    stated `30°` angle, rewrite `sin(π/6)=1/2`, and obtain exactly `15/2`;
    unfold the three answer predicates and isolate choice C by cases.

66. **`PhyXMiniProblems/problem_phyx_mini_0689.lean`.**
    Eliminate the positive hoop time from horizontal and vertical projectile
    equations, prove the denominator in the launch-speed square formula
    positive from reachability, choose the positive square root, and certify
    the calibrated radical against the displayed answer list.

67. **`PhyXMiniProblems/problem_phyx_mini_0690.lean`.**
    Express car 1's traveled distance in `2.5 h`, apply the cosine rule with
    the `40°` included angle to the lake triangle, divide by positive meeting
    time for car 2's speed, and bound the cosine/radical expression to prove
    choice C is closest.

68. **`PhyXMiniProblems/problem_phyx_mini_0691.lean`.**
    Rewrite both projectile coordinate laws: cancel their common vertical
    terms, use opposite horizontal directions and cosine symmetry, then
    simplify the Euclidean norm of `(2vt cos θ,0)` with nonnegative time,
    speed, and acute-angle cosine.

69. **`PhyXMiniProblems/problem_phyx_mini_0692.lean`.**
    Use perpendicular radial/tangential acceleration to convert the total
    magnitude squared to a sum of squares, substitute `a_r=v²/L` and the
    gravitational tangential component at each requested position, then take
    the nonnegative square root and normalize the answer readout.

70. **`PhyXMiniProblems/problem_phyx_mini_0693.lean`.**
    Equate the no-bounce and two-leg ranges to derive
    `sin θ=1/sqrt 5` on the acute branch; substitute this into both flight-time
    sums to obtain `3/sqrt 10`, then bound `sqrt 10` tightly enough for
    `0.949` and unique choice C.

71. **`PhyXMiniProblems/problem_phyx_mini_0694.lean`.**
    Combine elastic energy, kinetic energy, and conservation to prove
    `v²=8`, use nonnegative physical speed to select `sqrt 8`, and certify
    `2.75 < sqrt 8 < 2.85`; enumerate choices to prove exactly C reports the
    one-decimal launch speed.

72. **`PhyXMiniProblems/problem_phyx_mini_0695.lean`.**
    Expand work-energy over `0.5 m`: pull work `50`, friction `7.35`, and
    spring energy `10` give kinetic energy `653/20`; use `K=mv²/2` and speed
    nonnegativity for `sqrt(653/50)`, multiply by the `100 N` pull, and certify
    the final power display.

73. **`PhyXMiniProblems/problem_phyx_mini_0696.lean`.**
    Solve the two-mass center-of-mass equation with the `2.0 kg`, `0.5 kg`,
    and `0.5 m` readouts to get radii `0.1` and `0.4 m`; convert `40 rpm` to
    angular speed and derive `v₁=2π/15`, then prove the requested displayed
    tolerance using `pi` bounds.

74. **`PhyXMiniProblems/problem_phyx_mini_0697.lean`.**
    Evaluate the uniform rod's first-moment integral and cancel positive mass
    density to get `x_cm=L/2=0.8`; substitute rigid rotation's
    `a_t=α|x-x_cm|` and `α=6`, prove the pointwise profile, then use endpoint
    values to refute position-independent tangential acceleration and finish
    the answer predicates.

75. **`PhyXMiniProblems/problem_phyx_mini_0698.lean`.**
    Sum the three point-mass contributions to obtain
    `I=107/50000`; reduce Physlib's inertia-tensor contraction for an
    axle-aligned angular velocity to `Iω²/2`, solve the `0.1 J` equation as
    `ω²=10000/107`, select positive `ω`, and certify its displayed choice.

76. **`PhyXMiniProblems/problem_phyx_mini_0699.lean`.**
    Substitute the center-of-mass drop `L/2`, hinge inertia `mL²/3`, and
    `v_tip=ωL` into energy conservation, cancel positive `m,L`, and obtain
    `v_tip²=3gL`; choose the nonnegative square-root branch and prove the
    numerical answer interval.

77. **`PhyXMiniProblems/problem_phyx_mini_0700.lean`.**
    Integrate annular shells for a uniform disk or directly specialize the
    supplied annular inertia law at inner radius zero, simplify to
    `I=MR²/2`, and unfold the displayed expression to close recorded choice C.

78. **`PhyXMiniProblems/problem_phyx_mini_0701.lean`.**
    Derive the perpendicular moment arm `0.2 cos 30°=sqrt 3/10`, apply the
    signed cross-product convention for the downward force to obtain
    `-10 sqrt 3`, then bound `sqrt 3` to show `-17` (B) is strictly closest,
    leaving the inconsistent recorded C as metadata.

79. **`PhyXMiniProblems/problem_phyx_mini_0702.lean`.**
    Locate the uniform beam's center of mass from the support using the figure,
    multiply its standard-gravity weight by the perpendicular lever arm, and
    normalize units to `3920 N·m`; unfold the displayed torque table for
    choice C.

80. **`PhyXMiniProblems/problem_phyx_mini_0703.lean`.**
    Solve center of mass and lever arms as `60,60,30 m`, sum point-mass inertia
    to `5.4·10⁸`, add the thrust couple to `4.5·10⁶ N·m`, divide for
    `α=1/120`, and insert this in constant-angular-acceleration kinematics for
    the final requested angular velocity/answer.

81. **`PhyXMiniProblems/problem_phyx_mini_0704.lean`.**
    Compute the propeller inertia from the mass geometry, use torque balance
    for constant angular acceleration, convert the target rpm to rad/s, and
    solve duration as `40π/27`; apply rational `pi` bounds to prove the
    `4.6±0.1 s` and strict closest-choice inequalities.

82. **`PhyXMiniProblems/problem_phyx_mini_0705.lean`.**
    Derive radius `1/20 m`, apply the parallel-axis law for
    `I=3/320`, sum gravity and applied torques with the stated signs to
    `149/40`, divide by positive inertia for angular acceleration, and decide
    the nearest displayed value by exact rational cases.

83. **`PhyXMiniProblems/problem_phyx_mini_0706.lean`.**
    Eliminate tension and angular acceleration from translation, rotation, and
    no-slip laws, substitute solid-cylinder inertia to derive
    `a=mg/(m+M/2)` in arbitrary coherent units, then combine
    `distance=½at²` with positive time to obtain the square-root fall-time
    formula and numerical choice.

84. **`PhyXMiniProblems/problem_phyx_mini_0707.lean`.**
    Resolve forces and take torques about the elbow to solve tendon force
    `7875/2 N`; return to vertical/horizontal force balance for elbow reaction
    `6975/2 N`, then enumerate displayed forces to prove the recorded tendon
    choice and the prose-requested elbow choice D are each uniquely nearest.

85. **`PhyXMiniProblems/problem_phyx_mini_0708.lean`.**
    Subtract the two Newtonian energy equations to get the change in speed
    squared, specialize the stopped initial state, substitute the surface and
    initial separations plus constants, select the positive square root, and
    certify its displayed speed by rational bounds.

86. **`PhyXMiniProblems/problem_phyx_mini_0709.lean`.**
    Use torque balance about the floor and horizontal/vertical force balance to
    show every slip-preventing coefficient is at least
    `½ cot 60°=1/(2sqrt 3)`, construct equilibrium at equality to prove
    `IsLeast`, and bound the radical for closest choice C.

87. **`PhyXMiniProblems/problem_phyx_mini_0710.lean`.**
    Derive the limiting line-of-action geometry
    `h_max=b/tan θ`, rewrite `tan 30°=1/sqrt 3` and the base width to obtain
    `(15/2)sqrt 3`, use the static-stability law for maximality, and certify
    choice C's unique closeness.

88. **`PhyXMiniProblems/problem_phyx_mini_0711.lean`.**
    Sum the two endpoint point-mass inertias to `ml²/2`, expand angular
    momentum as `I·2πf`, cancel positive common mass and `2π`, and derive
    `l_i²f_i=l_f²f_f`; substitute the before/after length and frequency
    readouts to solve the displayed final rotation rate.

89. **`PhyXMiniProblems/problem_phyx_mini_0712.lean`.**
    Rewrite the disk and loop inertia formulas with equal radius and stated
    masses to prove their inertias equal, solve the conserved total angular
    momentum equation for common final angular velocity using positive total
    inertia, then substitute initial angular velocities and decide the answer.

90. **`PhyXMiniProblems/problem_phyx_mini_0713.lean`.**
    Combine impact angular-momentum conservation with swing energy conservation
    to obtain the squared bullet-speed balance; substitute the rigid assembly
    inertia and geometric rises, prove all factors positive to select the
    positive square root, simplify `cos(π/6)`, and certify the displayed speed.

91. **`PhyXMiniProblems/problem_phyx_mini_0714.lean`.**
    Equate launch kinetic energy to the Newtonian surface escape-energy deficit,
    cancel positive rocket mass, derive `v²=2GM/R`, and select the positive
    square root; substitute Earth calibration and certify the recorded choice
    with rational radical bounds.

92. **`PhyXMiniProblems/problem_phyx_mini_0715.lean`.**
    Derive spherical and flat-Earth launch speeds separately from their
    potential laws and energy conservation, selecting positive square-root
    branches; rewrite the percentage-error definition as their normalized
    difference and bound the calibrated radicals to prove the nearest displayed
    percentage.

93. **`PhyXMiniProblems/problem_phyx_mini_0716.lean`.**
    Write each star's centripetal balance about the center of mass, use
    `r₁+r₂=d` and the common angular speed `2π/T`, and eliminate force/radii to
    obtain `d³=G(m₁+m₂)T²/(4π²)`; substitute calibrations, take the positive
    cube root if needed, and certify the answer.

94. **`PhyXMiniProblems/problem_phyx_mini_0717.lean`.**
    Rewrite the SHM trajectory with graph-derived amplitude, phase, and period;
    solve `cos` on one period using the acute `arccos(4/5)` branch to get the
    two stated times, then certify the later time's hundredth-second interval
    and closest-choice inequalities using inverse-cosine bounds.

95. **`PhyXMiniProblems/problem_phyx_mini_0718.lean`.**
    Substitute the data into the ideal bungee equilibrium, angular frequency,
    phase, and velocity formula at `2 s`; normalize the exact trigonometric
    expression, establish a certified interval within `0.05 m/s` of choice C,
    and compare the same interval with all alternatives.

96. **`PhyXMiniProblems/problem_phyx_mini_0719.lean`.**
    Expand the exact pendulum law near bottom equilibrium, use the imported
    sine derivative/remainder theorem to prove the required local linearization
    contract, identify the Physlib oscillator frequency, convert angular to
    cyclic frequency, and certify the final numerical choice.

97. **`PhyXMiniProblems/problem_phyx_mini_0720.lean`.**
    Compute circular cup area, use the ideal-vacuum pressure difference and
    detachment force balance to solve mass as `20265π/784`, prove any
    sustainable mass is no larger via the statics inequality, and bound `pi`
    to establish unique closeness to `81 kg`.

98. **`PhyXMiniProblems/problem_phyx_mini_0721.lean`.**
    Read the elevation difference as `3/5 m`, apply hydrostatics from the
    atmospheric open surface to the closed top, substitute density, gravity,
    and pressure conversion, and use exact/rational bounds to prove the
    atmosphere readout and unique closest displayed pressure.

99. **`PhyXMiniProblems/problem_phyx_mini_0722.lean`.**
    Use cube geometry for displaced volume, Archimedes for buoyancy, and static
    balance `B=W+T` to solve `T=147/50 N`; unfold the tenth-newton and nearest
    predicates and prove choice C plus uniqueness by finite cases.

100. **`PhyXMiniProblems/problem_phyx_mini_0723.lean`.**
    Equate buoyancy and weight in both liquids, cancel common positive area and
    gravity to get `ρ_u d_u=ρ_w d_w`, substitute `1000`, `5.8`, and `4.6`
    for `29000/23`, then enumerate displayed densities for the target's
    nearest/unique predicates.

101. **`PhyXMiniProblems/problem_phyx_mini_0724.lean`.**
    Apply circular area and continuity to obtain upper speed `45/4 m/s`;
    substitute both elevations, velocities, density, and lower pressure into
    Bernoulli to derive `18475/4 Pa=739/160 kPa`, then normalize the displayed
    pressure answer.

102. **`PhyXMiniProblems/problem_phyx_mini_0725.lean`.**
    Combine reservoir/nozzle boundary conditions, continuity, and Bernoulli
    across the specified elevations to solve the inlet deficit exactly as
    `153125 Pa`; convert to atmospheres and decide the tenth-atmosphere
    rounding, nearest status, and unique choice C.

103. **`PhyXMiniProblems/problem_phyx_mini_0726.lean`.**
    Expand the tangent right triangle
    `(R+h)²=R²+d²`, cancel `R²`, and divide by positive `2h` for
    `R=(d²-h²)/(2h)`; substitute metre conversions to get `37209991/6`, then
    compare its kilometre value exactly with all displayed radii.

104. **`PhyXMiniProblems/problem_phyx_mini_0727.lean`.**
    Unfold astronomical-unit and light-year readouts to obtain their exact
    scale ratio, then use certified bounds for those Physlib constants to prove
    the `0.02·10⁻⁵ ly` tolerance and enumerate alternatives for unique nearest
    choice C.

105. **`PhyXMiniProblems/problem_phyx_mini_0728.lean`.**
    Use the gap convention to show each arrival adds one body depth, so twenty
    arrivals first make `5 m`; use the uniform arrival cadence to construct the
    twentieth arrival at `10 s`, prove all earlier elapsed times have fewer
    than twenty arrivals, and package the witness in the `IsFirstTime`
    predicate.

106. **`PhyXMiniProblems/problem_phyx_mini_0729.lean`.**
    Apply vehicle-number flux conservation to the stationary reference regime
    to derive gap `4L`; double it for the current `96 m` gap, substitute current
    values into the same conservation equation, and solve the signed shock
    velocity before normalizing its displayed answer.

107. **`PhyXMiniProblems/problem_phyx_mini_0730.lean`.**
    Write the relative stopping-distance equation at limiting noncollision,
    convert both train speeds from km/h, and solve the positive deceleration as
    `3025/3042`; prove it lies in the nearest-thousandth interval centered at
    `0.994`, then unfold choice C.

108. **`PhyXMiniProblems/problem_phyx_mini_0731.lean`.**
    Solve the horizontal ground-slope intersection as
    `t=h/(v tan θ)`, prove positivity and that no earlier positive contact
    occurs from the rising-line geometry, construct the impact-time witness,
    and certify its `1.3 s` displayed tolerance using tangent bounds at
    `4.3°`.

109. **`PhyXMiniProblems/problem_phyx_mini_0732.lean`.**
    Expand both green-trigger equations, cancel their common spatial offset,
    apply uniform platoon motion between signals 2 and 3, and divide by
    positive speed to obtain `delay=D₂₃/v` in every coherent length/time unit.

110. **`PhyXMiniProblems/problem_phyx_mini_0733.lean`.**
    Specialize the projection law to `12.5 sin 20°`, then use certified sine
    bounds to place the result in the `4.28±0.005 m` interval and outside every
    competing hundredth display; reuse the exact helper in the main theorem.

111. **`PhyXMiniProblems/problem_phyx_mini_0734.lean`.**
    Propagate the symmetric `60°` bifurcation direction equations through the
    trail tree from the nest to A, normalize accumulated angles modulo
    `2π`, and show the resulting displacement vector has zero horizontal and
    positive vertical component, hence direction `π/2`.

112. **`PhyXMiniProblems/problem_phyx_mini_0735.lean`.**
    Use orthogonality of the `22 m` strike-slip and `17 m` dip-slip components
    to apply Pythagoras and select the nonnegative magnitude
    `sqrt(22²+17²)`; compare rational squares to show it lies within `0.05 m`
    of `27.8`.

113. **`PhyXMiniProblems/problem_phyx_mini_0736.lean`.**
    Combine rolling without slip for half a revolution with rigid-wheel
    geometry to obtain displacement components `(πR,2R)`, cancel positive
    radius in the quadrant-I angle relation, and certify
    `degrees(arctan(2/π))` within `0.05°` of `32.5` and uniquely closest.

114. **`PhyXMiniProblems/problem_phyx_mini_0737.lean`.**
    Compute each requested displacement vector and divide by its positive
    elapsed time; for A-to-C obtain exactly `5/600=1/120 m/s`, compare squared
    magnitudes to prove it uniquely least, and discharge the `0.0083 m/s`
    display tolerance.

115. **`PhyXMiniProblems/problem_phyx_mini_0738.lean`.**
    Eliminate flight time using horizontal motion for the diving release and
    substitute into vertical motion to derive the stated height expression;
    insert calibrated data, certify its interval around `897.48 m`, and prove
    the whole-metre match and unique closest recorded choice C.

116. **`PhyXMiniProblems/problem_phyx_mini_0739.lean`.**
    Use zero vertical velocity at the positive apex to eliminate apex time and
    derive `H=(v₀ sin θ)²/(2g)`; substitute `v₀`, angle, and standard gravity
    to get `135/2 m`, then simplify the final displayed-height predicate.

117. **`PhyXMiniProblems/problem_phyx_mini_0740.lean`.**
    Solve horizontal wall incidence for the unique positive impact time,
    substitute it into vertical projectile motion for the predicted height,
    then insert the readouts and certify the computed expression within
    `0.5 m` of `12 m` and strictly closer to C than to alternatives.

118. **`PhyXMiniProblems/problem_phyx_mini_0741.lean`.**
    Derive the initial horizontal and vertical velocity components from the
    two roof-flight readouts and constant-gravity equations, prove the initial
    vector lies in the acute quadrant, express its angle with `arctan`, and
    certify the `40.4°` tenth-degree interval and uniqueness.

119. **`PhyXMiniProblems/problem_phyx_mini_0742.lean`.**
    Eliminate apex time between velocity, position, and sight-line equations
    to get `tan θ=2 tan φ`; use the acute-angle hypotheses and tangent
    injectivity to select `θ=arctan(2 tan φ)`, then prove a certified interval
    around `55.46°` for `φ=36°` and unique choice C.

120. **`PhyXMiniProblems/problem_phyx_mini_0743.lean`.**
    Eliminate the nonzero equal-height flight time from horizontal and vertical
    motion to derive `R=v² sin(2θ)/g`, substitute the cannonball readouts, and
    use certified trigonometric bounds to establish the numerical range and
    displayed answer.

121. **`PhyXMiniProblems/problem_phyx_mini_0744.lean`.**
    Bound the trajectory below the `3.6 m` plateau and prove first contact
    occurs on the incline before `6 m`; use the ramp equation to show the
    landing displacement has slope `3/5`, hence angle `arctan(3/5)`, and
    certify the `31.0°` rounding and unique choice C.

122. **`PhyXMiniProblems/problem_phyx_mini_0745.lean`.**
    Use the four-second vertical displacement and gravity law to solve initial
    vertical speed, use the `60°` landing-velocity angle for horizontal speed,
    combine components by Pythagoras into the defined exact expression, and
    certify its displayed speed choice with tangent/radical bounds.

123. **`PhyXMiniProblems/problem_phyx_mini_0746.lean`.**
    Eliminate the positive landing time between projectile and slope equations
    to prove the predicted horizontal intersection, convert through track
    geometry to landing drop, and use certified sine/cosine bounds to place the
    closed form near `1.11338 m`, proving the `1.11 m` match and unique C.

124. **`PhyXMiniProblems/problem_phyx_mini_0747.lean`.**
    Equate the vertical position at `t=1` and `t=5` to solve initial vertical
    velocity, substitute either time with release height `1 m` and
    `g=9.8` to obtain wall height `51/2 m`, and unfold choice C's exact
    displayed value.

125. **`PhyXMiniProblems/problem_phyx_mini_0749.lean`.**
    Read the graph intercepts through Galilean horizontal motion to derive
    relative `v₀x=10 m/s` and flight duration `4 s`; use equal launch/landing
    heights for `v₀y=19.6 m/s`, then combine components and the sled velocity
    according to the target's frame convention and certify the answer.

126. **`PhyXMiniProblems/problem_phyx_mini_0750.lean`.**
    Specialize the cosine rule to the two radar ranges and `123°` angle to
    derive the exact squared displacement; prove positivity and compare that
    value with the squares of `1030.5` and `1031.5`, using certified cosine
    bounds, then enumerate displays for unique nearest-metre choice C.

127. **`PhyXMiniProblems/problem_phyx_mini_0751.lean`.**
    Subtract the figure's horizontal coordinates for `13 ft`, solve the
    positive hoop-crossing time from horizontal motion, eliminate it in the
    vertical equation to derive the exact required-speed radical, prove its
    denominator positive from reachability, and certify the displayed foul-shot
    speed.

128. **`PhyXMiniProblems/problem_phyx_mini_0752.lean`.**
    Eliminate flight time from horizontal range and vertical displacement to
    derive the defined required launch-speed expression, selecting the
    positive radical branch; substitute the kilometre, height, angle, and
    gravity readouts and use certified trigonometric/radical bounds around
    `255.5289 m/s` to prove the `255.5` match and unique choice C.
