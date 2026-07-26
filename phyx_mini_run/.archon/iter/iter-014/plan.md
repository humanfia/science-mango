# Iteration 014 Plan

## Batch contract

- Preserve exactly the 128 Current Objectives in their existing order:
  16 mandatory proof-Review retries followed by 112 new accepted-open targets.
  No `proof_review_exhausted` target is present.
- Eligibility shortfall: 0. The fixed objective list exceeds the required
  `max_parallel = 32` occupancy by 96 targets; Plan does not mutate that
  loop-selected list. The executor must not silently reinterpret this as a
  compliant 32-target dispatch.
- Preserve every theorem signature and physical hypothesis. Derive all
  numerical choices from the governing laws; discharge square-root,
  trigonometric, and inverse-trigonometric readouts with certified rational
  bounds and explicit physical-branch conditions.

## Per-target proof strategy

1. **`PhyXMiniProblems/problem_phyx_mini_0070.lean` (retry 1/3).**
   Specialize the unit-covariant sightline law to centimeters and rewrite the
   two figure readouts to obtain `run * tan (π/6) = 50`. Rewrite
   `tan (π/6)`, use positivity of `√3` to derive `run = 50√3`, and prove
   `1.73 < √3 < 1.75` by squaring; unfold the rounding and choice definitions
   and close both `87 cm` claims from the resulting `86.5 < run < 87.5`
   interval. Keep denominator cancellation in a separate equality so the
   reviewed proof does not depend on an in-place `field_simp`.

2. **`PhyXMiniProblems/problem_phyx_mini_0071.lean` (retry 1/3).**
   Rewrite the grazing Snell law with the water/air readouts to get
   `sin θ = 100/133`. From the acute branch and
   `sin² θ + cos² θ = 1`, certify the cosine bounds needed for
   `1 ≤ tan θ ≤ 13/11`; combine these with
   `65 = depth * tan θ` and nonnegative depth to prove
   `55 ≤ depth ≤ 65`. Unfold the nearest-mark predicate, rewrite the
   `10 cm` spacing, and close `|depth - 60| ≤ 5`; obtain the formula conjunct
   directly from the geometry lemma.

3. **`PhyXMiniProblems/problem_phyx_mini_0072.lean` (retry 1/3).**
   Unfold `IsLeast` and the admissible-displacement set. Prove that the
   critical construction is admissible by choosing its refracted angle, using
   the side-A Snell law, perpendicular-side geometry, the water-air critical
   law, and all acute-branch hypotheses; for an arbitrary admissible
   displacement, use monotonicity of `sin`, `arcsin`, and `tan` on the
   certified principal intervals to obtain the lower bound. For choice C,
   reduce `tan (arcsin z)` to `z / √(1-z²)` after proving `|z| < 1`, substitute
   `n_water = 133/100`, `n_air = 1`, and the `10 cm` readout, then certify the
   `18.15 ≤ threshold ≤ 18.25` interval by squared rational bounds. Assemble
   the target from the two completed lemmas.

4. **`PhyXMiniProblems/problem_phyx_mini_0074.lean` (retry 1/3).**
   First derive the exact prism-index quotient from the two Snell equations
   and the parallel-base angle identities, cancelling only positive sine
   factors. Isolate the numerical work into rational interval lemmas for the
   small auxiliary angle, `sin`, `cos`, and `√3`, then bound the quotient
   strictly between `1.575` and `1.585`. Use that interval for the hundredth
   rounding claim and discharge uniqueness by a four-way choice split,
   rewriting each absolute value with an explicitly proved sign.

5. **`PhyXMiniProblems/problem_phyx_mini_0075.lean` (retry 1/3).**
   Obtain diffraction dominance from the stated resolution trend and rewrite
   the Rayleigh law to identify the local `theta`. Specialize the exact
   central-angle geometry and the paraxial remainder to millimeters, proving
   the chart distance positive before scaling the error inequality. Rewrite
   the diameter by the exact geometry, factor the difference as
   `distance * (centralAngleDiameterRatio theta - theta)`, and finish with
   `abs_mul` and monotonic multiplication by the positive distance.

6. **`PhyXMiniProblems/problem_phyx_mini_0080.lean` (retry 1/3).**
   Derive the exact cubic-cell size
   `0.26 / (√2 * sin (47π/450))` from diagonal plane spacing and first-order
   Bragg reflection, with a separate proof that the denominator is positive.
   Use certified rational bounds for `√2` and the sine (via a bounded Taylor
   estimate on the displayed acute angle) to place the quotient in
   `[0.5695, 0.5705)`. Rewrite the rounding predicate and prove unique
   closeness by splitting the four choices and fixing the signs of the
   absolute differences from the same quotient interval.

7. **`PhyXMiniProblems/problem_phyx_mini_0081.lean` (retry 1/3).**
   Divide the two Bragg equalities using positive crystal spacing and acute
   peak angles, thereby expressing the longer wavelength through the
   short-line readout and the ratio of the two sines. Certify a tight rational
   interval around each displayed peak angle using sine monotonicity on
   `[0, π/2]` and explicit Taylor bounds, yielding the existing
   `37 < wavelength_pm < 39`-strength interval. Use it to show choice C at
   `38 pm` is strictly closer than A, B, and D, with the `C` branch eliminated
   by the inequality hypothesis.

8. **`PhyXMiniProblems/problem_phyx_mini_0082.lean` (retry 1/3).**
   Specialize the Fraunhofer double-slit law at fringe orders one and two and
   rewrite the width, separation, and central-irradiance readouts to obtain
   exactly `56/π²` and `28/π²`. Prove a rational enclosure for `π²` from
   certified bounds on `π`, use positive-denominator division to establish
   the `5.7` and `2.9` display tolerances, and transport the first tolerance
   directly through `MatchesFirstFringeAnswer`.

9. **`PhyXMiniProblems/problem_phyx_mini_0084.lean` (retry 1/3).**
   Evaluate the interface phase-reversal law at air-oil and oil-water; the
   two half-turns cancel because both reflections are from lower to higher
   index. Substitute this zero phase difference, the `475 nm` wavelength,
   oil index `1.20`, and third-band order into the round-trip path and
   constructive-interference laws, then solve linearly for
   `t = 2375/4 nm`. Unfold nearest-nanometer matching and let exact rational
   normalization prove rounding to `594`, choice C.

10. **`PhyXMiniProblems/problem_phyx_mini_0088.lean` (retry 1/3).**
    Convert the graph's fifth-of-six minimum location to `750 nm` and use the
    first-minimum lemma to obtain an optical path difference of `λ/2`.
    Specialize the linear optical-path increment at `750` and `1200`, prove
    both positions lie in the controlled interval, and eliminate the common
    refractive-index increment to get `Δ(1200) = (4/5)λ`. Substitute this into
    the phase law and cancel the strictly positive wavelength to obtain
    `8π/5`.

11. **`PhyXMiniProblems/problem_phyx_mini_0089.lean` (retry 1/3).**
    Use the graph/interference helper to establish the material length
    `L = (5/4)λ`. At index `2`, rewrite the optical-path law with equal
    ambient baseline paths and air index one; then rewrite the phase law with
    the equal initial and reflection phases. Cancel `2π` and the positive
    wavelength explicitly to show the phase difference in wavelengths is
    `5/4`, and unfold the choice readout to obtain C.

12. **`PhyXMiniProblems/problem_phyx_mini_0090.lean` (retry 1/3).**
    Use the Euclidean geometry laws and readouts to normalize the two ray
    lengths to `√712 λ` and `√436 λ`, then rewrite propagation and the common
    initial phase to get the stated `Real.Angle` equality. For the choice
    result, prove rational upper and lower bounds for both square roots by
    squaring against their nonnegativity, deduce
    `5.8 ≤ √712 - √436 ≤ 5.9`, and settle each displayed alternative after
    rewriting the corresponding absolute-value signs.

13. **`PhyXMiniProblems/problem_phyx_mini_0091.lean` (retry 1/3).**
    Chain the two Snell laws through water and layer X, rewrite the phase-speed
    refractive-index model and the `48°`/`65°` readouts, and cancel the
    positive common factors to isolate the air-angle sine. Use the acute
    branch plus certified sine comparisons at `81.5°` and `82.5°` to trap the
    air angle strictly between those endpoints. This directly proves the
    half-degree agreement with `82°`; prove unique closeness to A by splitting
    B, C, and D and resolving each absolute-value sign from the same interval.

14. **`PhyXMiniProblems/problem_phyx_mini_0096.lean` (retry 1/3).**
    Separate the order proof from the numerical proof. For `IsGreatest`, show
    the predicted critical ray belongs to the TIR-permitting set using both
    Snell laws and complementary face geometry, then map any admissible ray
    through monotonic `sin`/`arcsin` on the physical intervals to prove it is
    no larger. For the readout, normalize the critical argument, establish it
    lies in `(-1,1)`, and apply the correctly oriented `arcsin` endpoint
    equivalences to prove `71.95° < predicted < 72°`; finish the explicit
    source-tolerance inequality for recorded `72.1°`. Avoid the reviewed
    proof's brittle mixed `toReal` and inverse-trig rewrites by proving each
    branch conversion once.

15. **`PhyXMiniProblems/problem_phyx_mini_0097.lean` (retry 1/3).**
    Rewrite the figure geometry to the entry angle `40°`, incidence at A
    `50°`, and grazing transmission `90°`. Specialize Snell at entry and A,
    use `sin 90° = 1`, and cancel the strictly positive air/glass indices to
    derive `sin thetaA = sin 40° / sin 50°`. Finally use the supplied
    `[0, π/2]` branch for `thetaA`, `Angle.coe_toReal`, and
    `Real.arcsin_sin` to identify it with the target inverse-sine angle.

16. **`PhyXMiniProblems/problem_phyx_mini_0098.lean` (retry 1/3).**
    Use the limiting-guidance laws and index readouts to derive the exact
    principal-branch sine equation for `theta_i`, proving the radicand and
    all square-root denominators nonnegative. Replace the long chained
    double-angle argument with local certified endpoint bounds: prove the
    sine value lies between the sines of `12.05°` and `12.15°` using rational
    Taylor remainders and standard rational bounds for `π`, then apply sine
    monotonicity on `[0, π/2]`. Convert that interval to degrees and close the
    nearest-tenth predicate for `12.1°`.

17. **`PhyXMiniProblems/problem_phyx_mini_0101.lean`.**
    Derive the predicted deviation formula by combining tangent-to-concentric-
    circle geometry with atmospheric Snell refraction and choosing the acute
    inverse-sine branch. Substitute `n = 1.0003`, `h = 20 km`, and
    `R = 6371 km`; certify the square-root and arcsine arguments, then prove a
    degree interval contained in `(0.22, 0.24)` by rational endpoint sine
    bounds. Transport the exact equality to the tolerance predicate and show
    A is closest by a finite choice split.

18. **`PhyXMiniProblems/problem_phyx_mini_0102.lean`.**
    Rewrite Snell's law at entry using `n_air = 1`, `n_glass = 1.80`, and
    incidence `66°`, and use the physical acute branch to identify the
    refraction angle. Substitute it into the parallel-plate displacement law
    `d = t * sin (i-r) / cos r` with `t = 2.40 cm`, proving `cos r > 0`.
    Establish certified rational sine/cosine bounds tight enough to place
    `d` in `[1.615, 1.625]`, then unfold the answer predicate for A.

19. **`PhyXMiniProblems/problem_phyx_mini_0103.lean`.**
    Prove the intermediate air-water relation by rewriting the perpendicular
    wall geometry in the water-surface Snell equation, converting the
    complementary wall angle from sine to cosine. Use Brewster's law with
    plastic index `1.61` to express that cosine, substitute ordinary-water
    and air indices, and bound the acute water angle by certified sine
    comparisons around `23.3°`. Use the resulting narrow interval to prove A
    strictly closer than `25.3°`, `24.2°`, and `22.6°`.

20. **`PhyXMiniProblems/problem_phyx_mini_0104.lean`.**
    Combine Brewster geometry, Snell, and the two Fresnel transmission
    coefficients to derive the axis ratio
    `2 n_air n_material / (n_air²+n_material²)`. Substitute this in the
    eccentricity definition; with `n_air = 1` and `n_material = 81/50`,
    square both sides and use nonnegativity to simplify the square root to
    `(n²-1)/(n²+1) = 4061/9061`. Rewrite the exact value in the nearest-choice
    predicate and discharge all three rivals by rational normalization,
    retaining `0.449` only as the closest displayed value.

21. **`PhyXMiniProblems/problem_phyx_mini_0105.lean`.**
    Specialize the ideal polarizer law at the graph's attained maximum and
    minimum angles. Use `0 ≤ cos² α ≤ 1`, the graph's global `25` upper and
    `5` lower bounds, and the extremizing witnesses to identify the constant
    unpolarized contribution with `5` and the polarized variation with
    `25 - 5 = 20 W/m²`. Convert the SI scalar equality back to the
    dimensionful irradiance and unfold the answer readout to obtain A.

22. **`PhyXMiniProblems/problem_phyx_mini_0106.lean`.**
    Specialize the spherical tangency and Snell laws to millimeters, rewrite
    all radius and index readouts, and use the physical acute-angle bounds to
    eliminate the trigonometric branches. Solve the resulting radius
    equations for the apparent radius, then apply the diameter law to obtain
    exactly `1377/20 mm`. Rewrite `68.9` as `689/10` and prove the
    half-tenth tolerance by `norm_num`.

23. **`PhyXMiniProblems/problem_phyx_mini_0107.lean`.**
    For the bend helper, combine the critical Snell equation
    `n₁ sin θc = n₂` with tangent-ray geometry, eliminate the acute
    sine/cosine terms, and clear the positive `n₁-n₂` denominator to derive
    `R = d n₂/(n₁-n₂)`. For the main timing theorem, use `t*v=L` and
    `v*n=c` separately for core and air, cancel only the positive speeds,
    subtract the travel times, and rewrite the `1000 m` path and air index
    one to obtain `1000*(n_core-1)/c`. Do not use the dimensionally
    incompatible centimeter answer metadata in this proof.

24. **`PhyXMiniProblems/problem_phyx_mini_0108.lean`.**
    Apply the spherical-mirror law to the `1.30 m` radius readout to prove the
    primary focal length is `13/20 m`. Rewrite normal adjustment and the
    eyepiece readout in one common unit, use positivity to cancel the focal
    length factor, and solve for magnification `650/11`. Normalize the
    nearest-tenth inequality around `59.1`, then split the four choices and
    use the same exact rational value to prove strict closeness to A.

25. **`PhyXMiniProblems/problem_phyx_mini_0109.lean`.**
    Use the calibrated grid origin, lens-center coordinate, backward-intercept
    coordinate, and `2 cm` spacing to normalize the axial separation to
    `9*2 = 18 cm`. Instantiate the principal-ray law for the depicted
    non-axis-parallel incoming ray whose outgoing segment is parallel to the
    axis; it identifies that backward intercept as the object-side focus.
    Rewrite the separation lemma to get the focal-length magnitude and unfold
    exact answer matching for A.

26. **`PhyXMiniProblems/problem_phyx_mini_0110.lean`.**
    Extract the paraxial image-location and magnification equations from the
    local axial Snell linearization, substitute the hemispherical radius,
    quinoline index, and display diameter, and solve for an explicit candidate
    greatest image diameter. Prove membership using the supplied real-image
    witness and prove the upper-bound half of `IsGreatest` from the physical
    image-domain inequalities. Certify that the candidate lies in the
    `24.05 ≤ D < 24.15` rounding interval, then show the other three displayed
    rounding intervals are disjoint to establish unique choice A.

27. **`PhyXMiniProblems/problem_phyx_mini_0111.lean`.**
    Rewrite the afocal magnification law with the `6.33 = 633/100` readout and
    the objective/eyepiece sign hypotheses; clear the nonzero objective focal
    length to obtain, for an arbitrary unit,
    `f₂ = -(100/633) f₁`. For the conditional calibration lemma, specialize
    to centimeters, substitute `f₁ = 95`, derive `-9500/633`, give the integer
    tenths witness `-150`, and prove the half-tenth error rationally. Keep the
    calibration out of the main scale-independent theorem.

28. **`PhyXMiniProblems/problem_phyx_mini_0112.lean`.**
    Derive `f(f₁+f₂-d)=f₁f₂` by eliminating the intermediate ray radius and
    second-lens image distance from the two paraxial laws, with all needed
    nonzero focal-length facts taken from the physical configuration. Apply
    it in centimeters and rewrite `f=30`, `f₁=12`, and `f₂=-18`; linear
    normalization yields `d=6/5`. The second conjunct follows immediately by
    unfolding `MatchesAnswer` and choice A.

29. **`PhyXMiniProblems/problem_phyx_mini_0113.lean`.**
    Normalize the side, nature, and orientation conventions so the height
    data give signed lateral magnification `m=-2`. Use the calibration-line
    hypothesis to extract the mirror's focal calibration, and combine it with
    the spherical-mirror equation and `m=-s'/s` to solve for the positive
    object distance `s=75/2 cm`. Rewrite the dimensionful centimeter readout
    and unfold choice A to finish by exact arithmetic.

30. **`PhyXMiniProblems/problem_phyx_mini_0114.lean`.**
    Specialize the reflected-ray vector equality to arbitrary units and
    project it onto both coordinates. Rewrite the mirror-hit rise using
    `b=a r²` and unfold the explicit specular-reflection direction; use
    positivity/nonaxiality to cancel the path length, radius, and the common
    positive normalization denominator. A ring normalization then leaves
    `4af=1`, and positivity of `a` permits division to conclude
    `f=1/(4a)` uniformly in units.

31. **`PhyXMiniProblems/problem_phyx_mini_0115.lean`.**
    Derive the four object endpoint coordinates from the `45°` pencil
    geometry and `4√2` axial/transverse projections. Apply the Gaussian lens
    and signed magnification laws at A and B, clearing denominators proved
    positive by the real-image hypotheses, to obtain the four stated exact
    image coordinates. Expand the squared endpoint distance, use
    `(√2)²=2`, and nonnegativity to identify the image length as
    `3200√10/593`; bound `√10` rationally to prove the `17.1 cm` rounding
    interval and strict closeness to A by choice splitting.

32. **`PhyXMiniProblems/problem_phyx_mini_0116.lean`.**
    Unfold the destructive-depth set and use the normal-incidence round-trip
    phase law, the `790 nm` wavelength, refractive index `1.8`, and the least
    destructive order to prove that `79/720 µm` is a member. For any other
    destructive depth, use its nonnegative interference order to prove it is
    at least this candidate, completing `IsLeastDestructivePitDepth`. Prove
    unique closeness to `0.11 µm` by exact rational comparisons, and obtain
    the final lower bound on the depicted pit by applying the least property
    to its destructive-depth membership.

33. **`PhyXMiniProblems/problem_phyx_mini_0118.lean`.**
    Square the one-bounce ray-length equation, use the positive wavelength
    and constructive order to solve for
    `d = (4r²-(mλ)²)/(2mλ)`, and prove the denominator nonzero before
    division. The excerpt explicitly supplies no numerical `r`, `f`, or
    helium-speed readout, so do not fabricate `11.3 cm`: unless an existing
    premise really entails those values, leave the numerical target as an
    honest reported gap while closing the symbolic helper.

34. **`PhyXMiniProblems/problem_phyx_mini_0119.lean`.**
    Convert `0.900 m` to `900 mm`; identify the calibrated best-fit slope as
    `0.558 mm²`, rewrite the paraxial relation as `slope = λL`, and cancel the
    positive screen distance to obtain `λ = 0.00062 mm = 620 nm`. Unfold the
    nearest-nanometer predicate and close choice A exactly.

35. **`PhyXMiniProblems/problem_phyx_mini_0120.lean`.**
    Expand the three monochromatic fields and use
    `cos (x+φ)+cos (x-φ)=2 cos x cos φ` to derive the phasor factor
    `1+2 cos φ`. Characterize the least positive absolute maximum by the
    principal phase `2π`, substitute the paraxial phase law, and cancel the
    positive slit separation to obtain the distance `Rλ/d`.

36. **`PhyXMiniProblems/problem_phyx_mini_0121.lean`.**
    Rewrite the controlled thin-biprism image-separation law and adjacent
    fringe law with the stated refractive index, prism angle, source distance,
    and wavelength. Clear only positive denominators, derive a tight rational
    interval around `1.57 × 10⁻³ m`, and use disjoint display intervals to
    prove A is the unique matching choice.

37. **`PhyXMiniProblems/problem_phyx_mini_0122.lean`.**
    Use exact tangent projection and the `1.53 mm` fringe readout to solve for
    slit separation, then combine order-seven coincidence with the first
    diffraction minimum to derive
    `(791/5355)√(1+(153/250000)²) mm`. Bound the square root rationally to
    establish the `0.148 mm` rounding interval and exclude every rival choice.

38. **`PhyXMiniProblems/problem_phyx_mini_0123.lean`.**
    Convert frequency to wavelength using `c = λf`, apply the Rayleigh
    aperture law with the effective `77,000 km` baseline, and scale the
    resulting angle by the quasar distance through the paraxial geometry law.
    Keep light-year and kilometer conversions exact, then certify the
    displayed tolerances around `2.05 ly` and `1.94 × 10¹³ km` for A.

39. **`PhyXMiniProblems/problem_phyx_mini_0124.lean`.**
    From the `3 s` closure cycle and opposite membrane velocities derive the
    repeat pitch `d = 6v`. Apply the first-order slit-array law on the
    principal `arcsin` branch to the two signed spots, proving the positive
    and negative formulas separately; retain the velocity symbol because no
    numerical speed is source-grounded.

40. **`PhyXMiniProblems/problem_phyx_mini_0125.lean`.**
    Express the two adjacent bright-fringe positions by the constructive law
    and exact screen tangent geometry. Use acute-branch `arcsin` identities
    and certified trigonometric bounds to place their difference within
    `0.01 mm` of `6.00 mm`, then compare the resulting interval with all four
    displayed values to select B.

41. **`PhyXMiniProblems/problem_phyx_mini_0126.lean`.**
    Add the two whole-degree boundary-angle intervals from the figure to prove
    `97 ≤ width ≤ 99`. The four displayed widths are separated enough that
    this interval proves C (`98°`) uniquely closest by elementary absolute
    value bounds; reuse the exact choice readout for the final conjunct.

42. **`PhyXMiniProblems/problem_phyx_mini_0127.lean`.**
    Evaluate the two reflection phase reversals from the index ordering,
    rewrite the constructive thin-film law for the least positive order, and
    solve `4nt = λ` with `λ = 540 nm`, `n = 1.35` to get `t = 100 nm`.
    Unfold `IsLeast`, showing membership and that every positive green
    thickness has order at least the chosen one, then apply it to the depicted
    thickness.

43. **`PhyXMiniProblems/problem_phyx_mini_0128.lean`.**
    Prove both reflected rays receive the same half-turn, so the relative
    interface phase is zero. The thinnest destructive order then gives
    `4nt = λ`; substitute `550 nm` and `n = 1.38` to obtain `6875/69 nm`,
    and close the `99.6 nm` choice-C tolerance by rational arithmetic.

44. **`PhyXMiniProblems/problem_phyx_mini_0129.lean`.**
    Normalize the object and virtual-image distances in centimeters and use
    the signed thin-lens equation to derive `1/f = 3/100 cm⁻¹`, with all
    nonzero distances discharged explicitly. Rewrite the optical-power law in
    meters to obtain `+3 D`, then unfold the choice predicate for C.

45. **`PhyXMiniProblems/problem_phyx_mini_0130.lean`.**
    Use the lens-to-far-point geometry to prove the signed virtual-image
    distance is `-3/20 m`; the distant-object thin-lens law then yields
    `1/f = -20/3 m⁻¹`. Transport this through the optical-power law and prove
    `-20/3` lies in the nearest-tenth interval for `-6.7 D`, choice C.

46. **`PhyXMiniProblems/problem_phyx_mini_0131.lean`.**
    Rewrite the circular-aperture and atmospheric resolution laws with their
    stated calibrations, cancel positive wavelength factors, and derive the
    exact improvement ratio. Bound it against the midpoints of the displayed
    choices to prove `9×`, choice D, is nearest; do not use the conflicting
    recorded choice C as a premise.

47. **`PhyXMiniProblems/problem_phyx_mini_0132.lean`.**
    Substitute `λ = 4 cm` and `D = 300 m` into the Rayleigh law, normalize
    units, and obtain exactly `61/375000 rad`. Prove that rational value falls
    only in C's displayed `1.6 × 10⁻⁴ rad` interval.

48. **`PhyXMiniProblems/problem_phyx_mini_0133.lean`.**
    Read the signed radii `R₁ = 22 cm` and `R₂ = 46 cm` from the figure/sign
    convention, then substitute them and `n = 3/2` into lensmaker's equation.
    Clear the nonzero radii to get `f = 253/300 m`, and verify the
    nearest-hundredth-meter predicate for choice C.

49. **`PhyXMiniProblems/problem_phyx_mini_0134.lean`.**
    Solve the two Gaussian lens equations and separation relation in
    centimeters to obtain `dᵢA=30`, `dₒB=dᵢB=50`. Use the signed
    magnification laws to get stage factors `-1/2` and `-1`, then rewrite the
    composition law and normalize their product to the supported `+1/2`.

50. **`PhyXMiniProblems/problem_phyx_mini_0136.lean`.**
    Solve the thin-lens equation for object distance `357/3386 m`, keeping the
    screen and focal distances positive. Substitute it into the transverse
    width law to derive exactly `5079/875 m`, then prove its nearest-tenth
    readout is `5.8 m`, choice C.

51. **`PhyXMiniProblems/problem_phyx_mini_0137.lean`.**
    Differentiate the exact on-axis Snell relation and local ray-geometry
    identities at zero, simplify their derivatives, and cancel the positive
    index/distance factors to establish
    `n_water d' = n_air d`. Substitute `d = 1 m`,
    `n_water = 4/3`, and `n_air = 1` to obtain `d' = 0.75 m` and C.

52. **`PhyXMiniProblems/problem_phyx_mini_0138.lean`.**
    Chain Snell's law across the two parallel faces, cancel the positive glass
    index, and use injectivity of sine on the physical acute branches to prove
    the emergent angle equals the incident `π/3`. Rewrite its sine as
    `√3/2`, bound `√3` around the thousandth display, and show C (`0.866`) is
    uniquely matching.

53. **`PhyXMiniProblems/problem_phyx_mini_0139.lean`.**
    Rewrite the convex focal law with `R = 16 m` to get `f = -8 m`; solve the
    Gaussian equation at `dₒ = 10 m` for `dᵢ = -40/9 m`. The signed
    magnification law then gives `m = 4/9`; normalize the nearest-hundredth
    error for `+0.44`, choice C.

54. **`PhyXMiniProblems/problem_phyx_mini_0140.lean`.**
    Use the curvature readout and focal law to derive `f = 15 cm`, then solve
    the signed mirror equation at `dₒ = 10 cm` for `dᵢ = -30 cm`. Substitute
    into `m=-dᵢ/dₒ` to obtain the upright magnification `+3` and unfold choice
    C.

55. **`PhyXMiniProblems/problem_phyx_mini_0141.lean`.**
    Convert the body/eye measurements to prove the eye height is `3/2 m`.
    Apply the plane-mirror virtual-image and limiting sightline geometry to
    show the lower mirror edge bisects the eye-to-floor height; combine the
    two equalities to obtain `3/4 m`.

56. **`PhyXMiniProblems/problem_phyx_mini_0142.lean`.**
    Use specular reflection at the first mirror to retain the `15°`
    surface-relative angle, then use perpendicularity to convert it to `75°`
    at the second surface. A second specular-reflection rewrite gives both the
    outgoing angle and `thetaFive` as `75°`; finish the target by assembling
    these derived equalities.

57. **`PhyXMiniProblems/problem_phyx_mini_0143.lean`.**
    Cancel the intermediate glass index by chaining the two parallel-face
    Snell equations, yielding the direct air-water sine relation. Substitute
    the standard indices and incident angle, prove the water angle lies in
    the `31.15°`–`31.25°` interval using certified sine bounds on the acute
    branch, and discharge rounding and unique closeness for C.

58. **`PhyXMiniProblems/problem_phyx_mini_0144.lean`.**
    Solve the sequential thin-lens equations for the three stated stage
    distances, then use the two transverse-size laws to derive ratios `13/23`
    and `92/113`. Cancel the positive intermediate/candle heights to obtain
    the product `1196/2599`, and prove its `0.46` display and nearest-choice C
    claims by rational comparison.

59. **`PhyXMiniProblems/problem_phyx_mini_0145.lean`.**
    Rearrange the far-bottom relation
    `width = depth * tan θ_water`, proving `tan θ_water ≠ 0` from the acute
    physical branch. Derive the water angle from Snell's law at the
    `13°` air readout, certify its tangent bounds, and show
    `width/tan θ_water` lies in the `6.04 ± 0.005 m` interval for C.

60. **`PhyXMiniProblems/problem_phyx_mini_0146.lean`.**
    Apply entry Snell refraction at `45°`, use equilateral-prism geometry to
    express the exit incidence angle, and apply exit Snell refraction on the
    acute physical branches. Certify rational sine/arcsine bounds placing the
    emergence readout in the `56.15°`–`56.25°` interval, then exclude A, B,
    and D.

61. **`PhyXMiniProblems/problem_phyx_mini_0147.lean`.**
    Prove the depicted incidence sine is `√2/2`; translate air-side TIR and
    water-side transmission into the strict bounds
    `√2 < n < (133/100)√2`, proving both set inclusions. Bound `√2` tightly
    enough to match endpoints `1.41` and `1.88`, and derive the sensor
    large-signal iff no-liquid statement from the two operating modes before
    assembling the target.

62. **`PhyXMiniProblems/problem_phyx_mini_0148.lean`.**
    Solve the second lens equation to get object distance `204/5 cm`; subtract
    the `30 cm` center separation to identify the first lens's signed image
    distance as `-54/5 cm`. Substitute this and the `25 cm` object distance
    into the first thin-lens equation, obtaining `f₁=-1350/71 cm`, then prove
    the nearest-tenth match to C.

63. **`PhyXMiniProblems/problem_phyx_mini_0149.lean`.**
    Use the upright/inverted observations to bracket the positive focal length
    strictly between `5` and `15 cm`. Rewrite the equal-magnitude
    magnification laws for the two trials and eliminate their signed image
    distances to force the midpoint value `10 cm`; the answer table then
    makes C unique.

64. **`PhyXMiniProblems/problem_phyx_mini_0150.lean`.**
    For each wavelength, rewrite entry Snell refraction, the equilateral-prism
    angle sum, and exit Snell refraction; use the supplied physical branches
    to identify the exit `toReal` with the declared forward
    `snellPredictedEmergenceRadians`. Keep both refractive indices symbolic
    because no grounded dispersion table supports numerical angles.

65. **`PhyXMiniProblems/problem_phyx_mini_0151.lean`.**
    Evaluate the air-oil and oil-water reflection reversals to obtain relative
    phase `-1` half-turn. With the second yellow band's order `m=1`, rewrite
    the path/constructive laws as `4nt=3λ`; substituting `n=1.50` and
    `λ=580 nm` gives `t=290 nm`, choice C.

66. **`PhyXMiniProblems/problem_phyx_mini_0152.lean`.**
    Combine the gas-cell double-pass optical-path increment with the counted
    fringes, vacuum index, cell length, and wavelength readouts, cancelling
    the positive cell length to derive `2071427/2062500`. Compare this exact
    rational against the millionth display intervals to select C.

67. **`PhyXMiniProblems/problem_phyx_mini_0153.lean`.**
    Eliminate the solar angular diameter between the distant-object geometry
    and central projection law to derive
    `f = imageDiameter * distance / sunDiameter`. Convert all supplied lengths
    to meters and normalize to `45/28 m`, then prove the nearest-tenth and
    strict closest-choice claims for C.

68. **`PhyXMiniProblems/problem_phyx_mini_0154.lean`.**
    Apply linear thermal expansion to each half-bar and the symmetric
    Pythagorean geometry to derive the stated square of the center rise. Use
    nonnegativity to take the positive square root, certify a rational
    interval around `0.075415 m`, and show `0.075 m`, choice D, is uniquely
    closest.

69. **`PhyXMiniProblems/problem_phyx_mini_0155.lean`.**
    Convert the figure's `30°` surface angle to `60°` from the normal, then
    use entry Snell and the acute branch to obtain the exact in-glass
    direction `arcsin(√3/3)` and prove it is below the incident angle. Bound
    its degree readout tightly enough for the displayed `35.3°` interval and
    establish the unique recorded choice without assuming it.

70. **`PhyXMiniProblems/problem_phyx_mini_0156.lean`.**
    Convert `2.00 cm` and `100 nm/s` to `1/50 m` and `10⁻⁷ m/s`; substitute
    these and aluminum's `23 × 10⁻⁶ K⁻¹` coefficient into
    `v = αd(dT/dt)`. Cancel the positive factors to obtain `5/23 K/s`, then
    verify the nearest-thousandth readout `0.217`, choice D.

71. **`PhyXMiniProblems/problem_phyx_mini_0158.lean`.**
    Eliminate the paraxial incident/refracted slopes between the ray geometry
    and first-order Snell law to prove `s' = s n₂/n₁`, with `n₁ ≠ 0` from
    physical positivity. Substitute the bubble's true center depth `5/2 cm`
    and keep `n_water/n_glass` symbolic; do not infer the ungrounded numerical
    choice B.

72. **`PhyXMiniProblems/problem_phyx_mini_0159.lean`.**
    Solve the Gaussian thin-lens equation with `f=50 cm`, `s=200 cm` to obtain
    `s'=200/3 cm`. Substitute this into the transverse-diameter law with
    object diameter `4 cm` to get `4/3 cm`, then prove its one-decimal match
    to `1.3 cm`, choice B.

73. **`PhyXMiniProblems/problem_phyx_mini_0160.lean`.**
    Use the graph-derived `f=10 cm` calibration and requested `p=14 cm` in the
    mirror equation to derive `q=35 cm`. Rewrite the signed magnification law
    as `m=-q/p`, normalize to `-5/2`, and unfold the displayed answer
    predicate for D.

74. **`PhyXMiniProblems/problem_phyx_mini_0161.lean`.**
    Compose plane-mirror imaging in water with the return refraction to prove
    the two index-weighted depth relations in an arbitrary unit. Substitute
    the stated bulb height, pool depth, and air/water indices in the final
    relation, cancel the positive water index, and finish the target's exact
    distance and answer readout.

75. **`PhyXMiniProblems/problem_phyx_mini_0162.lean`.**
    Unfold the first-visible condition and apply the grazing
    method-of-images similar triangles across the three equal corridor spans
    to derive distance `d/2`. Rewrite the burglar-to-mirror physical distance
    and `d=3 m` to obtain `3/2 m`, then unfold choice D.

76. **`PhyXMiniProblems/problem_phyx_mini_0163.lean`.**
    Use the plane-mirror virtual source and figure spans to prove its distance
    to P is `3d`, while the direct source is at `d`. Substitute both into the
    inverse-square law to get reflected irradiance `I_direct/9`; combine the
    two contributions and normalize the requested intensity ratio/choice.

77. **`PhyXMiniProblems/problem_phyx_mini_0164.lean`.**
    Rewrite visible image positions with the canonical direction-indexed set
    using the optics and sightline classification. Prove the three canonical
    directions injective so the finite set has `ncard = 3`, then unfold
    `visibleImageCount` and the recorded choice D for every visible monster.

78. **`PhyXMiniProblems/problem_phyx_mini_0166.lean`.**
    Convert four flash intervals to half a cycle at `5000/min`, yielding
    period `12/125 s` and frequency `125/12 Hz`. Use the pictured second
    harmonic to get `λ=1/2 m`, derive the wave speed, tension, and finally
    mass `2304/125 g`; compare that exact value with the displayed-choice
    precision rather than replacing it by a rounded premise.

79. **`PhyXMiniProblems/problem_phyx_mini_0167.lean`.**
    Eliminate buoyancy and weight from vertical equilibrium to derive
    `T=(m-ρV)g`. Substitute the diver mass, displaced volume, freshwater
    density, and standard gravity to obtain exactly `392 N`, then unfold
    choice A.

80. **`PhyXMiniProblems/problem_phyx_mini_0168.lean`.**
    Write the equal-arrival equation for the air and water sound paths,
    substitute the two calibrated speeds and depicted geometry, and solve the
    positive linear equation for `19524/215 m`. Prove
    `round (10d)=908` and strict closeness to `90.8 m`, choice A, by rational
    bounds.

81. **`PhyXMiniProblems/problem_phyx_mini_0169.lean`.**
    Prove the collinear path difference equals the nonnegative speaker
    displacement and derive `λ=343/725 m` from the acoustic wave law. Show the
    first positive destructive order is `λ/2 = 343/1450 m`, use order
    monotonicity for minimality, and discharge the displayed rounding/choice
    from that exact rational.

82. **`PhyXMiniProblems/problem_phyx_mini_0170.lean`.**
    Read the two path lengths as `3 m` and `1 m`, giving difference `2 m`.
    Characterize positive destructive frequencies by odd half-wavelengths;
    order zero maximizes wavelength at `4 m`, hence minimizes frequency at
    `344/4 = 86 Hz`. Prove the universal lower bound and unfold choice A.

83. **`PhyXMiniProblems/problem_phyx_mini_0172.lean`.**
    Convert both wire lengths/masses to SI, solve static force and torque
    balance for tensions `515/4 N` and `885/4 N`, and substitute them into the
    fundamental stretched-string law. Express the beat frequency as the
    absolute difference of the two radicals, bound it in a tight rational
    interval around `27.463 Hz`, and show displayed `27.3 Hz`, choice A, is
    uniquely closest.

84. **`PhyXMiniProblems/problem_phyx_mini_0173.lean`.**
    Derive `λ=c/f` for positive frequency and the geometric path difference
    `√(d²+x²)-x`. Prove this decreases from `d` toward zero, so a positive
    destructive position exists exactly above the cutoff `c/(2d)`; substitute
    the readouts to get `86 Hz` and establish both directions of the cutoff
    predicate.

85. **`PhyXMiniProblems/problem_phyx_mini_0174.lean`.**
    Rewrite the wave Snell law with the two speeds and `sin 30°` to obtain
    `sin θ₂=3/8`. Use the supplied acute branch to identify
    `θ₂=arcsin(3/8)`, then certify a degree interval around `22.0°` and prove
    choice C uniquely closest.

86. **`PhyXMiniProblems/problem_phyx_mini_0175.lean`.**
    Derive `λ=343/3000 m`, substitute it into the controlled first-minimum
    residual bound, and prove the actual sine stays in the stated finite-
    distance interval around `343/900`. Transfer this interval through the
    acute sine/tangent monotonicity and wall geometry to bound the listener
    offset tightly enough for the target's displayed choice.

87. **`PhyXMiniProblems/problem_phyx_mini_0176.lean`.**
    Convert the `60 cm` span to meters and use four fixed-end loops to prove
    `λ=0.30 m`. Substitute the `100 Hz` drive into `v=λf` to obtain
    `30 m/s`, then unfold choice D.

88. **`PhyXMiniProblems/problem_phyx_mini_0177.lean`.**
    Convert the five pictured loops into harmonic index five, then apply
    `2L=nλ` with `L=2 m` to get `λ=4/5 m`. The wave law at `40 m/s` gives
    `f=50 Hz`; rewrite the answer table to establish D.

89. **`PhyXMiniProblems/problem_phyx_mini_0178.lean`.**
    Square the transverse-wave-speed law before and after the fourfold tension
    increase, use positivity to select the factor `2`, and lift the scalar
    readout equality back to the dimensionful speed. Apply the unchanged
    four-antinode fixed-end law to cancel length and mode count, deriving the
    same factor two for frequency, answer D.

90. **`PhyXMiniProblems/problem_phyx_mini_0179.lean`.**
    Convert the `80 cm` tube length to `4/5 m`; the three displacement
    antinodes give two half-wavelength segments, hence `λ=L=4/5 m`.
    Substitute `f=500 Hz` into `v=fλ` to obtain `400 m/s` and unfold D.

91. **`PhyXMiniProblems/problem_phyx_mini_0180.lean`.**
    Eliminate wave speed, tension, and fixed drive frequency from the Hooke,
    stretched-string, and standing-wave laws to prove `n²xₙ` invariant.
    Substitute the three-antinode `8 cm` reference and requested
    two-antinode mode to get `x=18 cm`, then close choice D.

92. **`PhyXMiniProblems/problem_phyx_mini_0181.lean`.**
    Use the support geometry and torque balance to solve the wire tension,
    derive its linear density from the stated mass and length, and substitute
    both into the fixed-end fundamental law. Bound the resulting square root
    in the displayed tolerance for `13 Hz` and finish recorded choice D.

93. **`PhyXMiniProblems/problem_phyx_mini_0182.lean`.**
    Cross-multiply the equal-frequency, equal-length standing-wave and
    stretched-string laws to prove
    `μ_right n_left² = μ_left n_right²`. Insert the figure's loop counts and
    `μ_left=μ₀`, normalize the NNReal scalar action, and conclude
    `μ_right=(9/4)•μ₀`, answer D.

94. **`PhyXMiniProblems/problem_phyx_mini_0183.lean`.**
    Show the marked pile-1-to-pile-4 span contains three half-wavelengths;
    with `123 cm`, solve `2L=3λ` to get `λ=41/50 m`. Apply `v=fλ` at
    `400 Hz` to obtain `328 m/s`, the recorded choice D.

95. **`PhyXMiniProblems/problem_phyx_mini_0184.lean`.**
    Translate the two successive resonance lengths into the appropriate
    half-wavelength spacing, solve for the wavelength, and use `v=λf` to
    derive exactly `85750/71 Hz = 343/284 kHz`. Preserve the source-honest
    conclusion that this is about `1.208 kHz` and does not equal the recorded
    `12.1 kHz`; prove whatever nonmatching/display statement the fixed target
    requests by exact rational separation.

96. **`PhyXMiniProblems/problem_phyx_mini_0185.lean`.**
    Apply open-open fundamental geometry to the `2.0 m` rod to derive
    `λ=4 m`. Substituting aluminum's calibrated `6420 m/s` speed into
    `v=fλ` gives `1605 Hz`; prove its `1.6 kHz` display tolerance and unfold
    recorded choice D.

97. **`PhyXMiniProblems/problem_phyx_mini_0186.lean`.**
    Derive `λ=2 m` from the sound data and use the two 3-4-5 triangles to
    compute the initial paths `5,4,5 m`. After a one-meter move, all three
    paths are `5 m`; rewrite the common initial phase and propagation law to
    show exact constructive alignment, then discharge the target's minimum
    movement/answer condition from nonnegative-displacement geometry.

98. **`PhyXMiniProblems/problem_phyx_mini_0187.lean`.**
    Solve the principal constructive-forward/destructive-backward phase
    congruences under the shortest-spacing bounds to obtain separation `λ/4`
    and phase `π/2`. The delay-to-phase law makes the delay one quarter
    period; at `1000 kHz`, normalize the period to `1000 ns` and the delay to
    `250 ns`, choice D.

99. **`PhyXMiniProblems/problem_phyx_mini_0188.lean`.**
    Derive rope density `1/40 kg/m` and lower-end tension `196 N` from the
    readouts and static load. The transverse-wave law gives speed
    `√(196/(1/40)) = √7840`; prove tight rational square-root bounds around
    `88.5 m/s` and close choice A.

100. **`PhyXMiniProblems/problem_phyx_mini_0189.lean`.**
     Equate transmitted acoustic powers, rewrite plane-wave intensity in
     terms of bulk modulus, speed, frequency, and displacement amplitude, and
     cancel the preserved positive frequency. Substitute only the supplied
     area, air-modulus, and speed ratios to obtain the stated squared-
     amplitude relation, leaving incident amplitude and fluid bulk modulus
     explicit.

101. **`PhyXMiniProblems/problem_phyx_mini_0190.lean`.**
     Apply `c=λf` with `1480 m/s` and `262 Hz`, cancel the positive frequency,
     and derive `λ=740/131 m`. Compare this rational directly with all
     displayed meter values to prove recorded `5.64 m`, choice A, is closest.

102. **`PhyXMiniProblems/problem_phyx_mini_0191.lean`.**
     Use the doubled-distance hypothesis in the inverse-square law to prove
     `I₂=I₁/4`, with positivity permitting cancellation. Rewrite the decibel
     drop as `10 logb 10 4`; certify the logarithm between the rational
     endpoints needed for `6.0 ± 0.05 dB`, then finish choice A.

103. **`PhyXMiniProblems/problem_phyx_mini_0192.lean`.**
     Factor the nonzero incident amplitude from the rigid-wall pressure law
     to show silence iff the cosine phase vanishes. Apply the complete
     cosine-zero characterization, use nonnegative path bounds to parameterize
     all nodes as odd quarter-wavelengths, and specialize `n=0` to the first
     pictured position.

104. **`PhyXMiniProblems/problem_phyx_mini_0193.lean`.**
     Rearrange the moving-source wavefront law at positive emitted frequency
     to derive `λ_front=(c-v_s)/f`. Substitute `340`, `30`, and `300` to get
     `31/30 m`, then normalize the nearest displayed value `1.03 m`, choice A.

105. **`PhyXMiniProblems/problem_phyx_mini_0194.lean`.**
     Substitute the standard still-air, nominal emission, and receding-source
     readouts into the leftward Doppler law, proving all denominators positive,
     and normalize to `102900/373 Hz`. Show this lies in the nearest-hertz
     interval for `276 Hz`, recorded choice B.

106. **`PhyXMiniProblems/problem_phyx_mini_0196.lean`.**
     Rewrite the calibrated Doppler law as
     `300(340+15)/(340+45)`, with subsonic positivity justifying division.
     Normalize the ratio and prove its nearest-hertz match to `277 Hz`,
     recorded choice B.

107. **`PhyXMiniProblems/problem_phyx_mini_0198.lean`.**
     Eliminate Mach angle and horizontal flight distance from the cone and
     right-triangle laws to derive
     `delay = h√(M²-1)/(Mc)`. Substitute the stated parameters to obtain
     `25√33/7 s`, then square rational endpoints to certify the `20.5 s`
     choice-B tolerance.

108. **`PhyXMiniProblems/problem_phyx_mini_0199.lean`.**
     Cross-multiply Hooke equilibrium for the calibration and requested loads
     to eliminate stiffness and gravity, yielding proportional
     mass/compression. Substitute `200 kg`, `3 cm`, and `300 kg`, cancel the
     positive calibration mass, and normalize the requested lowering to
     `9/2 cm`.

109. **`PhyXMiniProblems/problem_phyx_mini_0201.lean`.**
     Rewrite the round-trip propagation law as `ct=2d`, substitute the
     textbook water speed and depicted distance, and derive exactly `t=1/7 s`.
     Compare this rational with every answer value to prove recorded
     `0.14 s`, choice D, is uniquely closest.

110. **`PhyXMiniProblems/problem_phyx_mini_0202.lean`.**
     Eliminate the post-impact composite speed between momentum conservation
     and spring-energy conservation to get the squared bullet-speed relation.
     Use positivity to select the stated positive radical, then certify
     rational square-root bounds tight enough for the fixed target's rounded
     speed/choice without treating the decimal as exact.

111. **`PhyXMiniProblems/problem_phyx_mini_0203.lean`.**
     Add the two exact Hooke forces for parallel identical springs to prove
     `k_eff=2k` in arbitrary readout units. Substitute this into the harmonic
     oscillator frequency/period law, use positivity to select the `√2`
     branch, and transport the resulting ratio to the target's displayed
     answer.

112. **`PhyXMiniProblems/problem_phyx_mini_0204.lean`.**
     Use the requested one-loop node geometry to fix the wavelength, then
     combine `v=λf`, `v²=T/μ`, taut-string tension, and pulley equilibrium.
     Substitute standard gravity and the readouts to solve
     `m=81/70 kg`, and verify its one-decimal match to `1.2 kg`, choice D.

113. **`PhyXMiniProblems/problem_phyx_mini_0205.lean`.**
     From the vertical SHM acceleration law, prove contact is preserved
     exactly when `Aω²≤g`; show `g/ω²` is both attainable and an upper bound,
     completing the maximum predicate. Rewrite `ω=2πf` with `f=2.8 Hz`, then
     use certified bounds for `π` to establish the `0.032 m` tolerance and
     closest choice D.

114. **`PhyXMiniProblems/problem_phyx_mini_0207.lean`.**
     Apply Physlib's harmonic-oscillator `ω_sq` result to each oxygen
     oscillator, bridge angular to cyclic frequency, and rewrite mass and
     stiffness readouts to obtain `k=m(2πf)²`. Substitute the oxygen-mass and
     observed-frequency data, normalize units, and certify the target's
     numerical spring-constant display.

115. **`PhyXMiniProblems/problem_phyx_mini_0208.lean`.**
     Evaluate the standing-wave profile and derivative at the fixed and free
     endpoints; use the boundary conditions and nonzero amplitude to derive
     `kL=(2n-1)π/2` for some positive `n`. Combine this with `k=2π/λ` in both
     directions, proving the full resonance iff
     `λ=4L/(2n-1)`.

116. **`PhyXMiniProblems/problem_phyx_mini_0209.lean`.**
     Use the limiting acoustic Snell law to derive the critical water angle,
     then combine the right-triangle bank geometry with angle monotonicity to
     prove the corresponding horizontal setback is safe and no smaller
     setback is safe. Certify its meter readout in the `0.44 m` displayed
     interval and unfold recorded choice D.

117. **`PhyXMiniProblems/problem_phyx_mini_0210.lean`.**
     Read the added midpoint node as two half-wavelength loops, compare with
     the original one-loop mode, and derive `2λ_after=λ_before`. Cancel the
     unchanged positive wave speed in `v=fλ` to prove
     `f_after=2f_before`, then discharge the target's frequency-ratio/choice
     statement.

118. **`PhyXMiniProblems/problem_phyx_mini_0211.lean`.**
     Rewrite constant-speed echo propagation as a two-leg distance, substitute
     `20 m` and `340 m/s`, and convert exactly to `2000/17 ms`. Compare this
     rational against the four answer readouts to show `120 ms`, recorded D,
     is uniquely closest.

119. **`PhyXMiniProblems/problem_phyx_mini_0212.lean`.**
     Use inverse-square spreading across the `30 m` to `300 m` change to prove
     far intensity is near intensity divided by `100`. Rewrite the decibel
     law using `log₁₀ 100 = 2` to derive a `20 dB` decrease, then substitute
     the measured near level and close the target's far-level answer.

120. **`PhyXMiniProblems/problem_phyx_mini_0213.lean`.**
     Use the node-to-antinode figure geometry to establish a quarter
     wavelength and derive the cross-multiplied relation `4Lf=v` for the
     branch vibration. Apply the emitted-tone equality to obtain the same
     relation for radiated sound and cancel positive `4L` only when proving
     the target's symbolic frequency equality; do not invent a missing wave
     speed.

121. **`PhyXMiniProblems/problem_phyx_mini_0214.lean`.**
     Compose the outbound and reflected-return Doppler factors with the
     rest-frame reflection equality, proving both denominators positive.
     Substitute `5000 Hz`, `343 m/s`, and `7/2 m/s`, normalize to
     `495000/97 Hz`, and prove nearest-hertz rounding to `5103`, choice D.

122. **`PhyXMiniProblems/problem_phyx_mini_0215.lean`.**
     Rearrange constant-speed propagation with positive air speed to prove
     `t=d/c`. Convert `1.55 km` to `1550 m`, substitute `343 m/s`, and obtain
     `1550/343 s`; exact rational comparison proves the `4.52 s` display,
     choice D.

123. **`PhyXMiniProblems/problem_phyx_mini_0216.lean`.**
     Apply Pythagoras to the `100 m` and `200 m` legs to show the displaced
     distance squared is five times the direct distance squared. The
     inverse-square law then gives an intensity ratio of five; rewrite the
     level advantage as `10 logb 10 5` and certify bounds sufficient for
     nearest-decibel rounding to `7 dB`, choice D.

124. **`PhyXMiniProblems/problem_phyx_mini_0217.lean`.**
     Convert the shell diameter to `3/20 m`, use the closed-open fundamental
     model to derive wavelength `4L=3/5 m`, and substitute `340 m/s` into
     `v=fλ` to obtain `1700/3 Hz`. Compare that exact rational with the
     displayed frequency choices and prove the fixed target's match/nearest
     claim without asserting the approximation as exact.

125. **`PhyXMiniProblems/problem_phyx_mini_0218.lean`.**
     Cancel common tension and density in the two fundamental string laws to
     show length is inversely proportional to frequency; apply the semitone
     ratio `2^(1/12)` to derive the two exact length formulas. Use certified
     monotonic power bounds for `2^(1/12)` to place the first-fret distance in
     the target's displayed tolerance and establish its answer choice.

126. **`PhyXMiniProblems/problem_phyx_mini_0219.lean`.**
     Derive `λ=343/474 m`, then express the two speaker-to-microphone paths
     from the figure and impose the first odd half-wavelength difference.
     Square only after proving both sides nonnegative, solve for the positive
     displacement, and certify its `0.429 m` rounding interval and target
     answer.

127. **`PhyXMiniProblems/problem_phyx_mini_0220.lean`.**
     Divide the Mach-cone triangle legs to obtain the positive acute tangent
     `29/40`, then use the principal `arctan` branch to identify the angle.
     Prove rational tangent comparisons at `35.5°` and `36.5°`, convert to the
     degree readout, and close the nearest-degree predicate for D.

128. **`PhyXMiniProblems/problem_phyx_mini_0221.lean`.**
     Eliminate the Mach angle from the cone law and right-triangle geometry to
     prove the general horizontal-distance formula
     `x=h√(M²-1)`, with nonnegative square-root branch justified by physical
     lengths. Convert the stated altitude to meters/kilometers, substitute the
     Mach number, and use squared rational bounds to finish the target's
     exact/rounded distance and displayed choice.
