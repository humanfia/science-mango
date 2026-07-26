# Iteration 011 Plan

## Batch contract

- Dispatch exactly the 32 preselected objectives in their existing order:
  six mandatory proof-Review retries followed by 26 new accepted-open targets.
- Eligibility shortfall: 0. No `review_exhausted` target is present.
- Preserve every theorem signature and physical hypothesis. For numerical
  optics, first derive the exact symbolic expression, then certify the printed
  tolerance with rational bounds for `pi`, `sin`, `tan`, `sqrt`, and inverse
  trigonometric functions; do not use an approximate value as a premise.

## Per-target proof strategy

1. **`problem_phyx_mini_0061.lean` (retry 1/3).** Normalize the reflection
   equality to a cosine equality between the two explicit vectors and the unit
   normal. Prove the two ray vectors nonzero from their first coordinates,
   cross-multiply the norm ratio with explicit nonzero side conditions, square
   it, rewrite both norm squares, and use the branch bounds to obtain `y = 9`
   by `nlinarith`. Avoid the fragile in-place `field_simp`/nested `rw` sequence
   from the reviewed attempt; finish by unfolding the strike-depth readouts.

2. **`problem_phyx_mini_0303.lean` (retry 1/3).** Rewrite the cyclic-to-angular
   frequency law and the `120 Hz` readout to prove `ω = 240 * pi` by `ring`.
   Unfold the recorded choice and nearest-whole predicate, rewrite `abs_lt`,
   normalize all rational endpoints, and close the two inequalities with
   explicitly type-checked Mathlib lower/upper bounds on `Real.pi` (rather
   than relying on the reviewed attempt's unverified lemma elaboration).

3. **`problem_phyx_mini_0333.lean` (retry 1/3).** Normalize both mechanical
   equilibrium laws and form an explicit area-multiplied pressure equality;
   cancel the positive disk area only after matching both sides syntactically,
   giving `p_final = 4 p_initial`. Chain the two ideal-gas laws with sealed,
   isothermal operation, substitute cylindrical volumes, then explicitly
   cancel area and positive initial pressure to derive the final height
   `1 m`. This replaces the reviewed attempt's shape-sensitive
   `apply mul_left_cancel₀` calls.

4. **`problem_phyx_mini_0346.lean` (retry 1/3).** Use the finite process-kind
   cases plus heat ordering to identify process `b` as isochoric and `c` as
   isobaric, excluding the adiabatic branches. Substitute `Q_b = 30`,
   `Q_c = 50`, `n = 0.3`, and Mayer's relation to derive
   `ΔT = 20000 / 2493`, hence the stated final Celsius temperature. Prove the
   nearest-choice conjunct by splitting the answer enum first and simplifying
   each exact rational absolute-value comparison; do not use a branch-wide
   `norm_num ... at hother ⊢` that leaves mismatched enum goals.

5. **`problem_phyx_mini_0380.lean` (retry 1/3).** Rewrite average density as
   total mass over the one-cubic-metre container, expand mass additivity and
   each density-times-volume law, and enumerate the four constituents with a
   proved `Finset.univ` equality. Let `simp` discharge insertion
   nonmembership after case analysis, substitute the four supplied volumes
   and air density, and finish with `ring`; avoid the brittle hand-selected
   `simp only` lemma list from the reviewed attempt.

6. **`problem_phyx_mini_0458.lean` (retry 1/3).** Derive the initial mass
   ratio and rewrite the closed-system energy balance with
   `m_B = 3/2 m_A`. Cancel the positive `m_A` in a separately stated
   syntactically matched equality, yielding the `2:3` specific-energy
   characterization. Normalize the final pressure relation to
   `P = (5/6) T`, unfold the named readouts before changing goals, and prove
   `P = 613 ↔ T = 3678/5` by two linear implications.

7. **`problem_phyx_mini_0000.lean`.** Close the parallel-interface helper by
   transitivity of `h_parallel.symm` and `h_phiOne`. At the oil-water
   interface, substitute indices and the `20°` angle into Snell's law, use the
   acute physical branch to identify `thetaPrime` with
   `arcsin ((1.48/1.333) * sin (20°))`, and certify that its degree readout is
   within `0.05` of `22.3`.

8. **`problem_phyx_mini_0001.lean`.** Substitute the air/water indices and
   `45°` incidence into Snell's law. Use positivity and the acute branch with
   `arcsin_sin`/sine injectivity to obtain
   `thetaTwo = arcsin (sin (45°) / 1.333)`, then prove the certified interval
   `31.95° ≤ thetaTwo ≤ 32.05°`.

9. **`problem_phyx_mini_0002.lean`.** Unpack the configuration's
   perpendicular-mirror geometry and reflection law. In the resulting right
   triangle, use the `1.25 m` opposite leg and reflected `40°` normal angle to
   derive the path length `1.25 / sin 40°`; rewrite `physicalDistance` and
   `siMetres`, then bound that expression strictly within `0.005 m` of
   `1.94 m`.

10. **`problem_phyx_mini_0003.lean`.** From Snell's law and the acute branch
    derive `sin r = 1/3` and `cos r = 2 * sqrt 2 / 3`. Substitute the
    `0.02 m` thickness into the path-length law, use the glass speed
    `c/(3/2)`, and solve the travel kinematics for time. Certified bounds on
    `sqrt 2` and the supplied light-speed readout then prove the
    `0.005e-10 s` answer interval.

11. **`problem_phyx_mini_0004.lean`.** First cancel the positive propagation
    speeds in entry Snell's law to prove the `9/10` sine relation. Next show
    the sum of the two tangents is positive from the acute hypotheses and
    divide the figure equation to obtain the geometry quotient. For the final
    theorem, use specular reflection to equate the two liver angles, insert
    the `50°`/`12 cm` readouts, identify the acute refracted angle by arcsine,
    and bound `12 / (2*tan r)` within `0.005 cm` of `6.30`.

12. **`problem_phyx_mini_0006.lean`.** Normalize the normal-entry and prism
    geometry, substitute the `45°` and `15°` relations into Snell's law, and
    derive `n^2 = 3/2`. Positivity selects
    `n = sqrt (3/2)`. Prove the `1.22` rounding interval with rational square
    bounds, then enumerate the other choices and compare exact absolute
    distances to establish unique nearestness.

13. **`problem_phyx_mini_0007.lean`.** Combine reflection with the pictured
    perpendicular branch to rewrite the refraction angle as `pi/2 - θ`.
    Convert Snell's law to `sin θ = n * cos θ`, use acute positivity to divide
    by `cos θ`, and obtain `tan θ = n`. Apply `arctan_tan` on the acute
    interval to conclude `θ = arctan n`; the vector readouts remain used only
    to ground the branch relation.

14. **`problem_phyx_mini_0008.lean`.** For red and violet separately,
    eliminate the two Snell equations and the apex-angle relation to express
    each deviation using principal-branch `arcsin` terms. Rewrite the figure's
    angular spread as violet deviation minus red deviation and certify the
    resulting degree interval around `4.6118°`, which lies within `0.005°` of
    choice C.

15. **`problem_phyx_mini_0009.lean`.** Unfold `CanEmerge` and use the physical
    angle ranges plus sine/arcsine monotonicity to characterize the strict
    emergence set by incidence angles above the displayed threshold and the
    tangent-inclusive set by angles at or above it. Prove the threshold is
    respectively the `IsGLB` and `IsLeast` endpoint, then certify the exact
    arcsine expression to the `27.9°` tolerance.

16. **`problem_phyx_mini_0010.lean`.** Substitute the three index readouts
    from the figure into `IsMaximumGuidedAngle`. Reduce the total-internal-
    reflection condition to the numerical-aperture inequality, prove the
    proposed arcsine value belongs and dominates all guided acute angles by
    monotonicity, and certify its degree readout in `[67.15, 67.25]`.

17. **`problem_phyx_mini_0011.lean`.** At `P`, use tangent transmission and
    Snell's law to identify the critical angle by `arcsin`; use facet geometry
    to obtain the entry refraction angle, then entry Snell's law and the
    physical branches to prove `rotationAngle = requiredRotationRadians`.
    Rewrite with the material readouts, bound its degree value around `2.83`,
    and enumerate the four choices to prove C is closest.

18. **`problem_phyx_mini_0012.lean`.** Define the candidate radius
    `R₀ = (n/(n-1)) • d`. On `NNReal.val`, use `n>1` and `d>0` to prove
    `d<R₀`, evaluate `(R₀-d)/R₀ = 1/n`, and invoke the TIR equivalence to show
    confinement. Conversely, any confining radius satisfies `R₀≤R` by
    clearing positive denominators. Package these facts as an `IsLeast` proof
    and use uniqueness with `hMinimum`.

19. **`problem_phyx_mini_0013.lean`.** Convert `a=1 μm`, `w=0.700 mm`, and
    `t=1.20 mm` to common readouts. The two right-triangle laws determine the
    plastic edge angles from their lateral half-widths; acute tangent
    injectivity removes branch ambiguity. Substitute those angles and
    `n=1.55` into Snell's law, identify the acute incidence angle by arcsine,
    and certify the `25.7°` nearest-tenth interval.

20. **`problem_phyx_mini_0015.lean`.** Derive
    `sin θ_c = 3/4` and, on the acute branch, `tan θ_c = 3/sqrt 7`. Construct
    the dimensionful depth with readout
    `(4.54/2)/tan θ_c`; use the escape-cone and raft-blocking definitions to
    prove it is unseen and that every unseen depth is no larger. Its boundary
    equation is immediate, and rational bounds on `sqrt 7` give the
    nearest-hundredth match to `2.00 m`.

21. **`problem_phyx_mini_0016.lean`.** Use prism geometry to get the internal
    surface-one angle `60°-42°=18°`. Combine the entry and critical Snell laws
    to eliminate both material indices, then use the physical principal
    branch to obtain the stated arcsine ratio. For `RoundsToNearestTenth`,
    choose the integer witness `275` and certify the degree error is below
    `0.05`.

22. **`problem_phyx_mini_0017.lean`.** Substitute the triangle angles,
    `n=3/2`, and `60°` incidence. Solve the entry Snell equation on the acute
    branch, transport that angle through the two mirror-geometry equations
    and specular reflection, and solve the exit Snell equation for the acute
    outgoing angle. Bound the resulting nested inverse-trig expression within
    `0.005°` of `7.91°`.

23. **`problem_phyx_mini_0018.lean`.** For the helper, rewrite the curved-entry
    Snell law using vacuum index one and the geometric identity
    `sin α=L/R`; divide by positive `n` and apply sine injectivity on the
    physical interval to obtain `β=arcsin(L/(nR))`. In the target, substitute
    `internal = α-β` into flat-exit Snell, then use the acute emergence branch
    to apply arcsine and reach the displayed closed form exactly.

24. **`problem_phyx_mini_0019.lean`.** Unfold critical cessation, simplify
    `sin (pi/2)=1`, and rearrange Snell's law to prove the threshold helper.
    In the main theorem substitute the `60°` point-P geometry and `n=1.66`,
    obtaining `n_threshold = 1.66 * sqrt 3 / 2`; certified square bounds put
    this strictly within `0.005` of `1.44`.

25. **`problem_phyx_mini_0020.lean`.** Unpack the circular figure readouts and
    the three optical laws. Use the parallel external directions, the
    rightmost mirror hit, and the inscribed half-angle relation to eliminate
    all ray angles from entry Snell, reflection, and exit Snell, deriving
    `n^2 = 2 + sqrt 3`. Physical positivity selects
    `n=sqrt(2+sqrt 3)`; rational nested-square bounds prove the `1.93`
    rounding interval.

26. **`problem_phyx_mini_0021.lean`.** Prove the helper by chaining the two
    upper-interface Snell equalities. Then unfold the final-TIR incidence set,
    substitute the four indices, and reduce it on the physical branch to the
    strict endpoint condition `sin θ > 5/8`. Sine/arcsine monotonicity proves
    `arcsin(5/8)` is its GLB; certified degree bounds prove the `38.7°`
    nearest-tenth result.

27. **`problem_phyx_mini_0022.lean`.** Prove the diameter helper directly from
    the two equal horizontal critical-ray runs and rotational symmetry.
    Substitute `n=1.52`, air index one, and `t=0.600`; critical Snell gives
    `sin θ_c=25/38`, hence `tan θ_c=25/sqrt 819` on the acute branch. Rewrite
    the diameter as `60/sqrt 819` and prove it lies in the `2.10±0.005 cm`
    interval.

28. **`problem_phyx_mini_0023.lean`.** Normalize all dimensional laws in SI.
    Use the `45°` entry and `76°` exit Snell equations together with the
    rectangular-path angle relations to solve the acute internal and bottom
    angles, then derive path length from the `0.50 m` drop. Eliminate the
    plastic speed with its refractive-index law, solve travel kinematics, and
    certify the nanosecond readout within `0.005 ns` of `3.40`.

29. **`problem_phyx_mini_0024.lean`.** Unfold the three mirror-membership and
    specular-reflection predicates and introduce the four segment direction
    vectors. Each reflection flips exactly the normal component; the open-
    segment hypotheses select the signs and hit order. Compose the three
    flips with return to the bottom-center aperture to show the initial
    horizontal and vertical component magnitudes agree, then use the entry
    angle range and `tan θ=1` (or cosine-angle injectivity) to conclude
    `θ=pi/4`.

30. **`problem_phyx_mini_0025.lean`.** Unfold the east-wall sweep, minimum,
    and maximum predicates. Rewrite the spot position and speed laws on the
    selected phase interval; monotonicity of `tan`/`sec²` from phase `0` to
    `pi/4` proves the endpoint extrema. Use the doubled reflected-ray angular
    speed and positive `ω` to cancel in the endpoint phase equation, yielding
    `end-start = pi/(8ω)` in every unit choice.

31. **`problem_phyx_mini_0026.lean`.** For the first helper, substitute the
    object-position readout and apply the upper-mirror universal reflection
    law at `d=p₁`. Rewrite the mirror-center separation to express that image
    as `p₁+h` above the lower center, then apply the lower-mirror law at that
    nonnegative distance for the final-image helper. In the target, compute
    the norm along the unit horizontal axis to show the requested distance is
    exactly `p₁+h`, selecting answer D.

32. **`problem_phyx_mini_0027.lean`.** Apply the thin-lens equation to the two
    object planes, clear their positive denominators, and solve for
    `q_a=q_b=105/4` and `q_c=q_d=140/3`. Substitute these values and the
    object-height readouts into transverse magnification to obtain
    `h_b'=-35/4` and `h_c'=-70/3`. Rewrite the target with the latter and
    close the `-23.3±0.05 cm` comparison by exact rational arithmetic.

## Blueprint corrections

- Replace stale “autoformalization task” theorem prose with the concrete
  current theorem and derivation in the listed chapters for `0013`, `0015`,
  `0018`, `0020`, and `0022`. These documentation-only corrections align the
  blueprint with the already accepted Lean statements and do not alter any
  hypothesis or conclusion.
