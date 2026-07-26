# Iteration 016 Plan

## Batch contract

- Preserve exactly the 128 loop-selected Current Objectives in their existing
  order: 11 mandatory proof-Review retries followed by 117 new accepted-open
  targets. No `proof_review_exhausted` target is present.
- Eligibility shortfall: 0. The fixed objective list exceeds the desired
  `max_parallel = 32` occupancy by 96 targets; Plan does not mutate or
  silently truncate that list. Execution must schedule the retry lanes first
  while respecting its actual concurrency limit.
- Preserve every theorem signature and physical hypothesis. Derive numerical
  answers only from the stated readouts and governing laws; certify radical,
  logarithmic, `rpow`, and `pi` bounds before discharging rounding or
  closest-choice predicates.
- The supplied blueprint excerpts contain no concrete chapter-level strategy
  defect, so no blueprint chapter is changed. Targets `0110`, `0118`, and
  `0120`, plus the standalone helper in `0169`, are underdetermined under
  their frozen hypotheses; keep their irreducible gaps explicit rather than
  adding unsupported data or weakening a statement.

## Per-target proof strategy

1. **`PhyXMiniProblems/problem_phyx_mini_0110.lean` (retry; 2/3 used).**
   Reuse the real-image witness to prove nonemptiness and retain the existing
   uniqueness-of-`IsGreatest`/choice argument. The hypotheses supply neither
   an attained upper bound nor a finite-ray/paraxial bridge, so leave the
   maximum-and-rounding subgoal as an explicit source-redraft obligation.

2. **`PhyXMiniProblems/problem_phyx_mini_0115.lean` (retry; 2/3 used).**
   Re-establish the exact endpoint image coordinates from the thin-lens laws,
   normalize the Euclidean length to `3200 * sqrt 10 / 593`, and prove the
   `17.1 cm` rounding and closest-choice claims from `sqrt 10 ^ 2 = 10`,
   nonnegativity, and rational `nlinarith` bounds.

3. **`PhyXMiniProblems/problem_phyx_mini_0116.lean` (retry; 2/3 used).**
   Use the optical-path and odd-half-wavelength laws to show the order-zero
   depth is `79/720 μm` and every destructive depth has nonnegative order.
   Apply the resulting least-element lemma to the depicted pit, then settle
   unique closeness to `0.11 μm` by exact rational absolute-value cases.

4. **`PhyXMiniProblems/problem_phyx_mini_0118.lean` (retry; 2/3 used).**
   Keep the proved symbolic axial-node-distance formula and the exact
   metre-to-centimetre conversion. No premise fixes radius, wavelength,
   frequency, sound speed, or order, so record the final equality to the
   numerical choice as an honest source-data blocker.

5. **`PhyXMiniProblems/problem_phyx_mini_0120.lean` (retry; 2/3 used).**
   Apply the closest-maximum lemma to obtain the exact symbolic
   `R * wavelength / d` result and use finite choice cases once a numerical
   equality is available. Since no premise specializes that ratio to `13/4`,
   retain precisely that numerical step as the source-redraft gap.

6. **`PhyXMiniProblems/problem_phyx_mini_0127.lean` (retry; 2/3 used).**
   Instantiate the odd-quarter-wave equivalence with order zero to show
   `100 nm` is constructive; for an arbitrary positive constructive
   thickness, extract its natural order and use nonnegativity to prove the
   lower bound. Insert the depicted thickness via physical positivity and
   the appearance hypothesis.

7. **`PhyXMiniProblems/problem_phyx_mini_0150.lean` (retry; 2/3 used).**
   Normalize the prism angle equation in `Real.Angle.toReal` using the stated
   physical angle intervals, cancel the positive air index in the two Snell
   equations, and apply `Real.arcsin_sin` on the certified emergence branch.
   Prove both labelled wavelengths through the same forward-model lemma.

8. **`PhyXMiniProblems/problem_phyx_mini_0158.lean` (retry; 2/3 used).**
   Prove the paraxial apparent-depth ratio by cancelling the positive
   refracted slope and glass index in the geometry/Snell equations, then
   rewrite the named figure media, `s = 5/2 cm`, and apparent-depth label to
   obtain the target verbatim.

9. **`PhyXMiniProblems/problem_phyx_mini_0160.lean` (retry; 2/3 used).**
   Specialize the mirror equation at `p = 14 cm` and `f = 10 cm`, prove the
   image distance is nonzero, and clear denominators to get `q = 35 cm`.
   Substitute into `m = -q/p` and normalize both the exact and displayed-D
   conjuncts.

10. **`PhyXMiniProblems/problem_phyx_mini_0169.lean` (retry; 2/3 used).**
    In the downstream theorem, combine the depicted collinear paths with the
    physical nonnegativity of the initial listener distance, derive
    `Δpath = displacement`, set the first odd half-wavelength to `343/1450 m`,
    and prove choice uniqueness rationally. The standalone geometry helper is
    false on its admitted negative-distance branch, so keep that helper gap
    explicit under its frozen signature.

11. **`PhyXMiniProblems/problem_phyx_mini_0308.lean` (retry; 1/3 used).**
    Rewrite the water-delay, air-calibration, interpreted-angle, and residual
    identities into one cross-multiplied equality. Subtract the exact
    far-field term, rewrite `abs_mul`, and scale the residual bound by the
    positive air-calibration speed.

12. **`PhyXMiniProblems/problem_phyx_mini_0343.lean`.** Specialize the ideal
    gas law at `b` and `c`, rewrite the common amount, constant, and isothermal
    temperature to equate `pV`, then substitute `p_b = 2`, `V_b = 0.2`, and
    `p_c = 0.5` to solve `V_c = 4/5 L` and unfold recorded choice B.

13. **`PhyXMiniProblems/problem_phyx_mini_0344.lean`.** Compute endpoint
    monatomic internal energies from `pV` to get `ΔU = 1200 J`; compute the
    two straight-leg trapezoid works and sum them to `1800 J`. Rewrite the
    first law to obtain positive `Q = 3000 J` and choice B.

14. **`PhyXMiniProblems/problem_phyx_mini_0345.lean`.** Use the adiabatic
    pressure ratio to derive `T₂ = 288.15 * (0.9)^(2/5)`, eliminate `nRT₁`
    with the initial ideal-gas equation, and obtain the stated exact `ΔU`.
    Prove a certified `rpow` interval tight enough to make choice B uniquely
    closest.

15. **`PhyXMiniProblems/problem_phyx_mini_0347.lean`.** Derive `p_a` from
    `pV^γ`, calculate each leg's work and heat in a common positive `pV`
    scale, and cancel that scale in the efficiency. Bound `4.5^(7/5)` (or the
    equivalent `rpow` expression) to prove displayed `31.9%` is closest.

16. **`PhyXMiniProblems/problem_phyx_mini_0348.lean`.** Sum the stated
    isochoric/adiabatic/isobaric work formulas into the temperature formula,
    then substitute `n`, `R`, `γ`, and the three temperatures to normalize
    the work to `1134861/5000 J`. Enumerate choices to prove B uniquely
    nearest.

17. **`PhyXMiniProblems/problem_phyx_mini_0349.lean`.** Derive the eight
    signed leg work/heat readouts from the rectangular `pV` coordinates and
    the diatomic energy law, aggregate net work and positive heat input, and
    cancel the positive base `p₀V₀` factor in the target efficiency.

18. **`PhyXMiniProblems/problem_phyx_mini_0350.lean`.** Prove the six leg
    readouts, reduce efficiency to `(2/7) * (1 - log 2)`, and establish
    rational bounds on `log 2` placing the result in `[0.087, 0.088)`.
    Unfold the truncation predicate for recorded choice B.

19. **`PhyXMiniProblems/problem_phyx_mini_0351.lean`.** Reduce the cycle
    algebra to `(3 log 3 - 2)/(3 + 3 log 3)`, prove denominator positivity,
    and certify a `log 3` interval yielding the `20.6%` rounding. Check all
    four displayed choices to prove none matches.

20. **`PhyXMiniProblems/problem_phyx_mini_0352.lean`.** Normalize all three
    state energies and straight-path works, use the first law for the signed
    heats, and sum to `W_net = 30000`, `Q_in = 270000`. Rewrite efficiency as
    `1/9` and discharge the `11.1%` tolerance rationally.

21. **`PhyXMiniProblems/problem_phyx_mini_0353.lean`.** Unfold the ideal
    refrigerator leg laws to the exact logarithmic COP, prove its denominator
    positive, and use certified logarithm bounds to trap it in the `6.23`
    hundredth window. Finish unique choice B by finite cases.

22. **`PhyXMiniProblems/problem_phyx_mini_0354.lean`.** Propagate the
    one-decimal temperature-readout intervals through the monatomic
    rectangular-cycle work and heat formulas to trap efficiency near `8/165`
    and percent near `160/33`. Compare that interval with every displayed
    choice to prove incompatibility.

23. **`PhyXMiniProblems/problem_phyx_mini_0355.lean`.** Sum the two
    isothermal Stirling works to `nR(T_H-T_C) log CR`, multiply by the cycle
    rate, and substitute the one-mole, `80 K`, ratio-10, `100 Hz` readouts.
    Bound `log 10` to prove `153 kW` and choice B uniquely.

24. **`PhyXMiniProblems/problem_phyx_mini_0356.lean`.** Integrate the
    adiabatic reference to `W = 3600 J`, use `Q = 0` and the first law for
    `ΔU = -3600 J`, and evaluate the requested straight trapezoid at
    `11550 J`. The first law then gives `Q = 7950 J`.

25. **`PhyXMiniProblems/problem_phyx_mini_0357.lean`.** Convert the circular
    `pV` diagram area to `100*pi J`, then use certified rational bounds for
    `pi` to place it within half a joule of `314`. Unfold the recorded answer
    metadata only after the physical equality is proved.

26. **`PhyXMiniProblems/problem_phyx_mini_0358.lean`.** Apply the
    straight-path trapezoid law to the two figure legs, normalize their unit
    conversions to `700 J` and `600 J`, and use the definition of total work
    to conclude `1300 J`.

27. **`PhyXMiniProblems/problem_phyx_mini_0359.lean`.** Use the two initial
    ideal-gas equations to fix the mole ratio, then use common final pressure
    and temperature so the final volume ratio equals it. Combine with the
    `80 cm` total length to solve the left width as `60 cm` and enumerate the
    displayed choices.

28. **`PhyXMiniProblems/problem_phyx_mini_0360.lean`.** Eliminate endpoint
    pressures and volumes using the sealed ideal-gas law, swept-cylinder
    geometry, and piston/spring force balance. Bound the remaining circular
    area expression with rational `pi` estimates to prove the depression is
    within `0.05 cm` of `3.8 cm`.

29. **`PhyXMiniProblems/problem_phyx_mini_0361.lean`.** Substitute the state-2
    `pV`, mole amount, and textbook gas constant into `pV=nRT` to obtain
    `75000/41 K`; subtract the exact Celsius offset and prove the whole-degree
    and strict closest-choice inequalities by normalization.

30. **`PhyXMiniProblems/problem_phyx_mini_0362.lean`.** Equate the two
    fixed-sample ideal-gas equations and cancel the common positive pressure
    to get `T₂/T₁ = 3`. Rewrite `900 °C` as `1173 K`, derive `3519 K`, and
    convert to `3246 °C`, choice A.

31. **`PhyXMiniProblems/problem_phyx_mini_0364.lean`.** Eliminate pressure
    and the two air volumes from Boyle, hydrostatic, and pipe-geometry laws to
    obtain `49L² + 500L - 1500 = 0`. Use positive length to select
    `(20 sqrt 340 - 250)/49`, then square rational bounds on `sqrt 340` for
    the `2.4 m` rounding and uniqueness.

32. **`PhyXMiniProblems/problem_phyx_mini_0365.lean`.** Normalize the two
    manometer laws to absolute pressures `880` and `790 mmHg`, apply constant
    volume `p/T`, and derive `431577/1760 K`. Convert to
    `-49167/1760 °C` and close answer A by rational cases.

33. **`PhyXMiniProblems/problem_phyx_mini_0366.lean`.** Use uniform-tube
    geometry to express both gas volumes in the unknown mercury-column
    length, combine Boyle's law with hydrostatic equilibrium, and use
    positivity to solve `L = 6/25 m`. Convert to `24 cm` and unfold choice A.

34. **`PhyXMiniProblems/problem_phyx_mini_0368.lean`.** Divide the ideal-gas
    laws at states 4 and 1 to obtain the `9/4` pressure-volume ratio, hence
    `T₄ = 53667/80 K`. Convert to `6363/16 °C` and prove rounding and unique
    closeness to `398 °C`.

35. **`PhyXMiniProblems/problem_phyx_mini_0369.lean`.** Rewrite one endpoint
    ideal-gas law with `p = 100000`, `V = 2`, `n = 80`, and `R = 8.31` to get
    `250000/831 K`; verify the second endpoint is consistent, then prove the
    `301 K` rounding interval exactly.

36. **`PhyXMiniProblems/problem_phyx_mini_0370.lean`.** Rewrite the affine
    path as `p(t)=100+100t`, `V(t)=2-t` and complete the square to maximize
    `pV` at `t=1/2` on `[0,1]`. Substitute `nR` for
    `1406250/4157 K` and settle the `338 K` rounding and uniqueness.

37. **`PhyXMiniProblems/problem_phyx_mini_0371.lean`.** Divide the sample mass
    by the helium molar mass to obtain `1/40 mol`, then specialize the
    state-1 ideal-gas law to derive `40000000/82057 K`. Convert to Celsius
    and check rationally that no displayed whole-degree choice lies within
    half a degree.

38. **`PhyXMiniProblems/problem_phyx_mini_0374.lean`.** Eliminate gas
    pressure and cylinder volume using the ideal-gas, circular-area, and
    piston-equilibrium laws to prove the symbolic height formula. Substitute
    the readouts and use certified `pi` bounds to trap the height between
    `23.512` and `23.513 cm`, making choice B uniquely closest.

39. **`PhyXMiniProblems/problem_phyx_mini_0375.lean`.** Express each endpoint
    pressure through atmospheric load plus Hooke force over piston area,
    express the volume change through swept distance, and combine the two
    ideal-gas equations. Use physical positivity to select the heated
    compression root and compare it with the four displayed values, yielding
    unique choice A.

40. **`PhyXMiniProblems/problem_phyx_mini_0377.lean`.** Evaluate the finite
    six-molecule sum by cases to `890`, rewrite the RMS law as
    `v² = 445/3`, and select the nonnegative square root. Square rational
    bounds around `12.2` to prove the half-tenth answer predicate.

41. **`PhyXMiniProblems/problem_phyx_mini_0378.lean`.** Expand the four
    histogram bars into weighted counts, normalize total count `10` and
    squared-speed sum `244`, and derive `rms = sqrt(122/5)`. Certify the
    `4.9 m/s` interval by squaring positive rational endpoints.

42. **`PhyXMiniProblems/problem_phyx_mini_0379.lean`.** Compute the graph
    slope as `4 J/K`, divide by `0.14 mol` through the constant-volume heat
    law, and normalize to `200/7`. Prove it lies in the integer-rounding
    interval for `29`, then rewrite choice A.

43. **`PhyXMiniProblems/problem_phyx_mini_0381.lean`.** Expand piston and rod
    circular/annular areas, insert the two pressures, mass, and gravity in the
    static force balance, and isolate the rod force. Use rational `pi` bounds
    to prove the `932.9 N` tenth-window and strict closest choice B.

44. **`PhyXMiniProblems/problem_phyx_mini_0382.lean`.** Substitute
    atmospheric pressure, gasoline density, gravity, and depth into the
    hydrostatic law, normalize the SI/kPa conversion to `124945/800`, and
    discharge the `156.2 kPa` rounding and unique choice B by cases.

45. **`PhyXMiniProblems/problem_phyx_mini_0383.lean`.** Rewrite the
    pressure-only valve balance with pressure difference `636 kPa` and area
    `11 cm²`, normalize units to `3498/5 N`, and compare exact rational
    distances to the four choices to prove B unique.

46. **`PhyXMiniProblems/problem_phyx_mini_0385.lean`.** Use positive
    densities, gravity, and layer heights to show pressure increases down
    each layer and is maximal at the bottom. Telescope both hydrostatic laws,
    substitute the calibration to obtain `453/4 kPa`, then prove the target
    rounding and closest-choice conjuncts by finite cases.

47. **`PhyXMiniProblems/problem_phyx_mini_0386.lean`.** Apply the prismatic
    displacement law to get `30 m³`, combine Archimedes and static equilibrium
    (cancelling positive gravity) for total supported mass `29910 kg`, and
    subtract the `10000 kg` tank mass to obtain choice-B ballast `19910 kg`.

48. **`PhyXMiniProblems/problem_phyx_mini_0387.lean`.** Derive gauge pressure
    as `rho*g*h`, use the figure angle and `sin 30° = 1/2` in the projection
    law to show `L = 2h`, and rewrite the `25 cm` head to obtain `L = 50 cm`
    and its answer choice.

49. **`PhyXMiniProblems/problem_phyx_mini_0389.lean`.** Solve the common final
    free-surface elevation from volume conservation and the two bottom
    offsets, then specialize hydrostatics to compute the two initial valve
    pressures (`111.1` and `130.8 kPa`) and the equalized final pressure.
    Use those certified intervals to finish the target flow/choice cases.

50. **`PhyXMiniProblems/problem_phyx_mini_0390.lean`.** Equate the connected
    fluid pressure under both freely supported pistons, expand both force
    balances, and cancel common outside pressure and positive gravity to get
    `m_B A_A = m_A A_B`. Substitute the areas and `m_A` to solve
    `m_B = 25/3 kg`, then unfold the displayed answer.

51. **`PhyXMiniProblems/problem_phyx_mini_0391.lean`.** Rewrite the
    differential mercury/manometer and orifice laws with the figure and
    property readouts, clear only physically nonzero denominators, and
    normalize the pressure drop to `2584/100 kPa`. Finish unique choice B by
    exact displayed-value cases.

52. **`PhyXMiniProblems/problem_phyx_mini_0392.lean`.** Integrate the linear
    hydrostatic pressure profile over the rectangular port, or apply the
    supplied resultant law, to obtain `rho*g*w*h²/2 = 882 kN`. Compare exact
    distances to the displayed forces to make `880 kN` choice B unique.

53. **`PhyXMiniProblems/problem_phyx_mini_0393.lean`.** Normalize the
    `25 m` water head to `245000 Pa`, add the required tank pressure to obtain
    `370 kPa` at the ground inlet, and transfer this through the ideal pump
    threshold law. Unfold `IsCorrectAnswer` and choice B.

54. **`PhyXMiniProblems/problem_phyx_mini_0394.lean`.** Use the figure
    elevations to prove total lift `155 m`, then substitute the endpoint
    pressure and hydrostatic-rise laws to obtain `1115962 Pa`. Convert to
    kPa and discharge the displayed rounding/choice target with rational
    inequalities.

55. **`PhyXMiniProblems/problem_phyx_mini_0395.lean`.** Expand the two
    circular face areas in the compound-piston balance and isolate chamber-B
    pressure as `6500000 - 1569064/pi`. Prove `pi` positive and use certified
    bounds to make `6 MPa` uniquely closest.

56. **`PhyXMiniProblems/problem_phyx_mini_0396.lean`.** Express piston travel
    from cylinder geometry, spring force from its linear law, and final gas
    pressure from static balance; substitute the rounded readouts and isolate
    the exact model value. Prove it lies only in the `515.3 ± 0.1 kPa`
    window.

57. **`PhyXMiniProblems/problem_phyx_mini_0397.lean`.** Use the reference
    state model to calculate tank-B volume, add rigid volumes and conserved
    masses, and normalize final specific volume to `63211/110000 m³/kg`.
    Unfold the reporting tolerance and prove choice B uniquely.

58. **`PhyXMiniProblems/problem_phyx_mini_0398.lean`.** Combine saturation
    pressure minus atmosphere with the `5 mm²` petcock area to get
    `0.486 N`; divide by positive `9.8 m/s²` and convert to
    `2430/49 g`. Compare with the displayed masses for unique recorded B.

59. **`PhyXMiniProblems/problem_phyx_mini_0399.lean`.** Divide the two
    constant-volume ideal-gas equations, convert both Celsius readouts to
    exact kelvins, and derive `p₂ = 1075970/5263 kPa`. Prove the `204.4`
    tenth-window and strict closest recorded B rationally.

60. **`PhyXMiniProblems/problem_phyx_mini_0400.lean`.** Add the conserved
    propane amounts from both initial tanks, use the uniform final pressure
    and total rigid volume, and solve the weighted ideal-gas relation for
    `10075/72 kPa`. Verify its one-decimal agreement with recorded B.

61. **`PhyXMiniProblems/problem_phyx_mini_0401.lean`.** Cancel fixed amount
    and volume in the initial/cooled ideal-gas equations, rewrite the
    temperature ratio, and solve the cooled pressure as `10/3 MPa`. Prove
    only choice B lies in the hundredth-MPa matching interval.

62. **`PhyXMiniProblems/problem_phyx_mini_0403.lean`.** Apply constant
    pressure boundary work to the figure's pressure and volume change,
    normalize units to `80 J` done by the gas, and rewrite the work-on-gas
    sign convention to obtain `-80 J`, displayed choice C.

63. **`PhyXMiniProblems/problem_phyx_mini_0405.lean`.** Convert `500 g` to
    `1/2 kg`, subtract the heating-curve plateau endpoints to get `60000 J`,
    and solve `Q = mL` for `120000 J/kg`. Rewrite the displayed latent-heat
    value for choice C.

64. **`PhyXMiniProblems/problem_phyx_mini_0406.lean`.** Prove the three
    named-unit conversion lemmas by the quantity covariance laws, then solve
    the insulated gas-water energy balance for `76555045/221771 K`. Insert
    that value into the final ideal-gas law, obtain the exact atmosphere
    readout near `2.83245`, and prove the target choice uniquely closest.

65. **`PhyXMiniProblems/problem_phyx_mini_0407.lean`.** Rewrite work on the
    gas as minus piston weight times positive rise, then expand piston mass as
    density times circular area times thickness. Positivity makes both
    expressions negative; unfold choice C's positive value to prove the
    stated conflict.

66. **`PhyXMiniProblems/problem_phyx_mini_0409.lean`.** Derive
    `Q_B = (7/2)pΔV` from the diatomic internal-energy, boundary-work, and
    first-law fields; substitute the figure values to get `28371/20 J`.
    Prove rounding to `1400 J` and unique choice C by rational cases.

67. **`PhyXMiniProblems/problem_phyx_mini_0410.lean`.** Use zero isothermal
    `ΔU` to identify heat with the logarithmic boundary work, substitute the
    `1/3` volume ratio and SI conversion, and bound `log 3` to trap the result
    near `-333.95 J`. Prove only displayed `-330 J` lies in the nearest-ten
    window.

68. **`PhyXMiniProblems/problem_phyx_mini_0411.lean`.** First expose
    `DimPressure.standardAtmosphere = 101325 Pa` by unfolding the Physlib
    constant and coherent-unit readout. Then specialize the isobaric and
    isochoric figure legs, normalize their `pV` changes in joules, and use the
    ideal-gas energy/first-law fields to close the requested heat/work choice.

69. **`PhyXMiniProblems/problem_phyx_mini_0412.lean`.** On the isochoric
    `2→3` leg set work to zero and rewrite monatomic internal energy as
    `(3/2)pV`; substitute the two state products and
    `1 atm·cm³ = 101325/10⁶ J` to get `-36477/400 J`. Prove the nearest-joule
    predicate for recorded C.

70. **`PhyXMiniProblems/problem_phyx_mini_0413.lean`.** Evaluate the
    straight-path trapezoid as `4053/80 J`, derive
    `ΔU = -12159/800 J` from `(3/2)Δ(pV)`, and combine them with the first law
    for the target heat. Normalize the resulting rational value and displayed
    answer cases.

71. **`PhyXMiniProblems/problem_phyx_mini_0414.lean`.** Prove all three leg
    heats from the monatomic energy and work laws, keeping the isothermal
    term as the exact multiple of `log 5`. Convert the negative `3→1` heat to
    `-1.01301933 kJ` and settle the `-1.01` rounding and nearest choice C.

72. **`PhyXMiniProblems/problem_phyx_mini_0415.lean`.** Obtain
    `p₂ = 1 atm` from the isotherm and
    `p₃ = (1/3)^(2/3) atm` from the adiabatic leg, then use zero isochoric
    work and `U=(3/2)pV` for the exact `Q₂₃`. Certify an `rpow` interval
    placing it near `-236.8 J` and uniquely closest to `-239 J`.

73. **`PhyXMiniProblems/problem_phyx_mini_0416.lean`.** Solve the endpoint
    spring/equilibrium laws for `0.08 m` compression, calculate monatomic
    `ΔU = 32.4 J` and spring work `6 J`, and apply the first law for
    `192/5 J`. Enumerate choices to characterize closest answer exactly as C.

74. **`PhyXMiniProblems/problem_phyx_mini_0417.lean`.** Apply the
    straight-leg work law to obtain `0`, `4053/50`, and `-4053/100 J`, sum
    them to `4053/100 J`, and compare exact distances to the displayed work
    values. Finish the recorded-C metadata equalities by simplification.

75. **`PhyXMiniProblems/problem_phyx_mini_0419.lean`.** Sum the four
    rectangular-leg works to `30 J`; combine the two rejected heats with
    closed-cycle first-law balance to derive `145 J` total heat input. Reduce
    efficiency to `6/29` and verify the `0.21` hundredth window for choice C.

76. **`PhyXMiniProblems/problem_phyx_mini_0420.lean`.** Compute the three
    straight-leg works as `0, 40, -30 J`, use cyclic energy balance with the
    two labelled incoming heats to get diagonal heat `-104 J` and input
    `114 J`, then reduce efficiency to `5/57`. Prove nearest-thousandth
    uniqueness for choice D.

77. **`PhyXMiniProblems/problem_phyx_mini_0421.lean`.** Compute triangular
    area/net work as `30 J`, sum the two displayed incoming heats to `315 J`,
    and use closed-cycle first-law balance to infer rejected heat
    `315 - 30 = 285 J`. Rewrite the displayed D answer.

78. **`PhyXMiniProblems/problem_phyx_mini_0422.lean`.** Derive `40 J` net
    work from the triangular area and use the `180 J` and `100 J` rejected
    heats with cycle closure to solve hot input `320 J`. Normalize efficiency
    to `1/8` and prove unique two-decimal choice D.

79. **`PhyXMiniProblems/problem_phyx_mini_0423.lean`.** Sum the signed
    adiabatic works to work input `41 J`, use the refrigerator first law for
    cold heat `64 J`, and reduce COP to `64/41`. Rationally prove the
    one-decimal rounding and strict closest choice D.

80. **`PhyXMiniProblems/problem_phyx_mini_0425.lean`.** Derive the eight
    rectangular-cycle leg energies, aggregate to `W_net = 2500 J` and
    `Q_in = 32465/2 J`, and reduce efficiency to `1000/6493`. Verify the
    hundredth tolerance around displayed `0.15`, choice D.

81. **`PhyXMiniProblems/problem_phyx_mini_0426.lean`.** Prove pressure,
    volume, and rpm-to-hertz conversions directly from dimensionful
    covariance. Then evaluate the three cycle-leg works from the figure,
    multiply net work per cycle by the converted shaft frequency, and
    normalize the exact power before discharging the displayed choice.

82. **`PhyXMiniProblems/problem_phyx_mini_0427.lean`.** Derive the missing
    pressures and temperatures and all six signed leg energies in the common
    initial `pV` scale; cancel that positive scale to get
    `(2-log 3)/10`. Bound `log 3` tightly enough for the `0.0901`
    ten-thousandth predicate and unique recorded D.

83. **`PhyXMiniProblems/problem_phyx_mini_0428.lean`.** Use the ideal-gas and
    adiabatic laws for `T₁ = 100 K` and `T₃ = 100/6^(2/3) K`, then compute
    the three heats and net work and cancel the positive `nR` factor.
    Certify an `rpow` interval proving the exact efficiency rounds to `0.32`.

84. **`PhyXMiniProblems/problem_phyx_mini_0429.lean`.** Derive
    `V₁ = 1000*4^(5/7)` from the adiabatic leg, calculate the isothermal and
    isobaric heats, and reduce efficiency to the stated `rpow/log` expression.
    Prove denominator positivity and certified bounds yielding unique `0.17`
    choice D.

85. **`PhyXMiniProblems/problem_phyx_mini_0430.lean`.** Normalize both
    endpoint `pV` products to `400 J`, use the adiabatic law for
    `T₂ = 300*4^(2/5)`, and derive heat input and net work including
    `-400 log 4`. Bound `rpow` and `log 4` to prove the `187 J` and efficiency
    rounding conjuncts uniquely select D.

86. **`PhyXMiniProblems/problem_phyx_mini_0431.lean`.** Expand the reversed
    monatomic cycle leg energies, multiply work per cycle by `60 Hz`, and
    normalize to `exactModeledInputPowerWatts`. Prove a certified radical or
    `rpow` interval around `227.2 W`, then discharge whole-watt rounding and
    strict unique choice D.

87. **`PhyXMiniProblems/problem_phyx_mini_0432.lean`.** Use the isotherm and
    pressure ratio to derive `V_max = 5000 cm³`, then calculate net work and
    positive heat input as the stated multiples of the positive base `pV`
    scale. Cancel the scale in efficiency and bound `log 5` for the displayed
    answer.

88. **`PhyXMiniProblems/problem_phyx_mini_0433.lean`.** Normalize all state
    energies, straight-leg works, and first-law heats to obtain
    `W_net = 2500 J` and `Q_in = 42500 J`. Reduce efficiency to `1/17` and
    prove the `0.059` thousandth window and unique recorded D.

89. **`PhyXMiniProblems/problem_phyx_mini_0434.lean`.** Solve the adiabatic
    volume relation for `V_max = 1000*4^(5/7)`, derive the hot/cold heats, and
    simplify efficiency to the stated `rpow` expression. Establish bounds
    around `0.14763` to prove the `0.15` rounding for D.

90. **`PhyXMiniProblems/problem_phyx_mini_0436.lean`.** Solve the two
    compartment energy balance for the common `5100/11 K`, then combine
    endpoint ideal-gas volumes with piston sweep geometry to isolate lift.
    Prove its millimetre tolerance around `0.050 m` and exclude every other
    displayed choice.

91. **`PhyXMiniProblems/problem_phyx_mini_0437.lean`.** Divide the two
    adiabatic temperature-volume relations to express the isochoric heat
    ratio as `1/r^(γ-1)`, rewrite the efficiency definition
    `1-Q_c/Q_h`, and use positive temperatures/heat to justify cancellation,
    yielding the standard Otto formula.

92. **`PhyXMiniProblems/problem_phyx_mini_0438.lean`.** Derive the Diesel
    cycle state temperatures and per-cylinder net work from the compression
    ratio and constant-pressure cutoff, then multiply by eight cylinders and
    the correctly converted rotational cycle rate. Use certified `rpow`
    bounds to make `211 kW` choice D nearest.

93. **`PhyXMiniProblems/problem_phyx_mini_0439.lean`.** Apply rigid-tank
    volume additivity and mass conservation, rewrite the known tank-A and
    final masses, and solve algebraically for
    `v_f = (2 + 7 v_B)/11`. Do not introduce an unstated water-table value or
    assert a numerical choice.

94. **`PhyXMiniProblems/problem_phyx_mini_0440.lean`.** Use the saturation
    and atmospheric pressures to obtain the net petcock pressure, multiply by
    `5 mm²`, divide by positive gravity, and normalize to `243/4900 kg` and
    `2430/49 g`. Prove nearest mass and uniqueness for choice D.

95. **`PhyXMiniProblems/problem_phyx_mini_0442.lean`.** Read the graph
    asymptote as `f = 20 cm`, specialize the Gaussian mirror equation at
    `p = 70 cm`, prove denominators nonzero from physicality, and solve
    `i = 28 cm`. Unfold `MatchesAnswerChoice` for D.

96. **`PhyXMiniProblems/problem_phyx_mini_0443.lean`.** Cancel fixed amount
    and volume in the two ideal-gas states, substitute the temperature ratio,
    and solve cooled pressure `10/3 MPa`. Check the nearest-hundredth
    predicate and uniqueness for this file's displayed choice D.

97. **`PhyXMiniProblems/problem_phyx_mini_0444.lean`.** Convert the saturated
    phase specific volumes into initial masses, use the equal tank-B volume
    and saturated-vapor endpoint to find transferred mass, and apply both
    mass balances to tank A. Normalize the quality increase and prove its
    `0.283 ± 0.0005` interval and unique choice D.

98. **`PhyXMiniProblems/problem_phyx_mini_0445.lean`.** Prove the millimetre,
    hour/minute, and flow-unit conversions from dimensional covariance, then
    convert the observed liquid-level drop to evaporated mass flow using
    container area and liquid density. Apply outlet specific volume to obtain
    volumetric flow per minute and match the displayed choice.

99. **`PhyXMiniProblems/problem_phyx_mini_0446.lean`.** Combine initial
    mixture volume, fixed mass, and spring-piston mechanics to place the
    target specific volume strictly between the `600 °C` and `700 °C` table
    rows. Use strict table monotonicity and the stated linear interpolation
    formula to prove the temperature is within `2 °C` of `641 °C`, uniquely D.

100. **`PhyXMiniProblems/problem_phyx_mini_0447.lean`.** Derive the general
    piston-drop formula by eliminating gas amount between endpoint ideal-gas
    equations and substituting final force balance plus swept volume.
    Normalize the readouts and bound the resulting value in the `5.3 cm`
    reporting interval, excluding other choices.

101. **`PhyXMiniProblems/problem_phyx_mini_0448.lean`.** Express tank-A final
    volume from piston sweep geometry, use isothermal ideal-gas inventory for
    each chamber, and impose total air conservation to solve final pressure
    `217 psia`. Simplify displayed D and prove uniqueness by cases.

102. **`PhyXMiniProblems/problem_phyx_mini_0449.lean`.** Use amount
    conservation and endpoint ideal-gas relations to derive cylinder-B final
    volume `4/15 m³`; apply constant external pressure boundary work to the
    volume increase and normalize to `40 kJ`. Rewrite displayed and recorded
    choice D.

103. **`PhyXMiniProblems/problem_phyx_mini_0450.lean`.** Obtain initial
    liquid volume `501/250000 m³` from `m v`, prove the affine spring-pressure
    integral equals endpoint-average pressure times `ΔV`, and substitute both
    endpoint volumes/pressures to get `808467/5000 kJ`. Finish the reporting
    tolerance and unique displayed choice.

104. **`PhyXMiniProblems/problem_phyx_mini_0451.lean`.** Use rigid volume and
    mass conservation with saturated-water table data to solve final quality
    `9891/22552`, then apply `W=0` and the first law to derive
    `98980769/112760 kJ`. Prove the one-decimal report `877.8 kJ` uniquely
    selects D.

105. **`PhyXMiniProblems/problem_phyx_mini_0452.lean`.** Read initial
    saturation pressure from the table, compute the linear-spring trapezoid
    work `701952797/40000000 kJ`, and calculate endpoint `ΔU = 1139/2 kJ`.
    Add them via the first law, then prove the result reports uniquely as
    `587 kJ`, choice D.

106. **`PhyXMiniProblems/problem_phyx_mini_0453.lean`.** Derive endpoint
    volumes/heights and final piston pressure from density, geometry, and
    force balance; integrate the changing hydrostatic load for the exact
    boundary work and normalize `ΔU = 2170.1 kJ`. Add by the first law and
    discharge the target tenth-kilojoule rounding/choice.

107. **`PhyXMiniProblems/problem_phyx_mini_0454.lean`.** Compute the
    moving-piston trapezoid work `-3541/200 kJ`, set fixed-volume work to zero,
    derive the mixture internal-energy change from the calibrated table, and
    apply the first law. Prove the total lies in the `-318.72 kJ` hundredth
    window and makes D unique.

108. **`PhyXMiniProblems/problem_phyx_mini_0456.lean`.** Sum the five
    component `m c` terms to total heat capacity `96400 J/K`, divide the
    `7,000,000 J` absorbed heat to solve the final temperature near
    `77.6 °C`, and compare exact rational distances to show `80 °C`, D, is
    uniquely closest.

109. **`PhyXMiniProblems/problem_phyx_mini_0457.lean`.** Use the all-water-
    expelled endpoint and cylinder geometry for final air volume `1 m³`,
    integrate the hydrostatic pressure path, compute ideal-air `ΔU`, and
    apply the first law for `220745 J`. Prove its `220.7 kJ` reporting
    predicate and unique D.

110. **`PhyXMiniProblems/problem_phyx_mini_0459.lean`.** Use the polytropic
    and ideal-gas endpoint laws to trap final temperature in `[668,669] K`,
    propagate the caloric-table interval through `Δu`, and derive work in
    `[121,122]` and heat in `[55,56.5] kJ/kg`. Compare that certified interval
    with the displayed choices to close the target.

111. **`PhyXMiniProblems/problem_phyx_mini_0460.lean`.** Solve the
    polytropic endpoint temperature and boundary work, use the cold-air
    caloric model for `ΔU`, and rewrite the first law to the named exact heat
    expression. Prove direct rational/`rpow` bounds making `-0.0147 kJ`
    uniquely choice D.

112. **`PhyXMiniProblems/problem_phyx_mini_0461.lean`.** Derive exit volume
    `10 cm³`, gas work `log 10 J`, and ambient displacement work `0.909 J`;
    substitute these in work-energy and select the nonnegative radical for
    bullet speed. Bound `log 10` and the square root tightly enough for the
    displayed-speed rounding and unique choice.

113. **`PhyXMiniProblems/problem_phyx_mini_0464.lean`.** Use R-410A endpoint
    properties and volume doubling to compute both internal energies, apply
    constant-pressure work on the first leg and zero work on the second, and
    sum through the first law. Prove the total is within `1 kJ` of displayed D
    and farther from every alternative.

114. **`PhyXMiniProblems/problem_phyx_mini_0468.lean`.** Apply Fourier's law
    separately to the copper and steel bars to obtain `77` and `502/25 W`,
    then use parallel-current additivity for `2427/25 W`. Normalize the
    one-decimal tolerance and finite cases to prove the target displayed
    choice.

115. **`PhyXMiniProblems/problem_phyx_mini_0469.lean`.** Divide endpoint
    ideal-gas equations under amount conservation, substitute the supplied
    pressure/volume/temperature ratios, and normalize to `144739/200 K`.
    Convert to `90109/200 °C` and prove the ten-degree rounding and unique
    closest choice B.

116. **`PhyXMiniProblems/problem_phyx_mini_0470.lean`.** Use equality of the
    cyclic initial/final states for `ΔU = 0`, evaluate the signed `pV` loop
    work, and apply `ΔU = Q - W` to obtain heat into the system `-500 J`.
    Take the absolute magnitude and rewrite recorded choice B.

117. **`PhyXMiniProblems/problem_phyx_mini_0474.lean`.** Use reversible heat
    ratio `Q_c/Q_h = 350/500` to derive rejected heat `1400 J` from the given
    hot input, then first-law work `600 J`. Reduce efficiency to `3/10`,
    convert to `30%`, and unfold recorded B.

118. **`PhyXMiniProblems/problem_phyx_mini_0475.lean`.** Simplify the first
    law with zero heat and zero work to prove internal-energy conservation,
    use equal compartments for `V_f = 2V_i`, and rewrite the ideal-gas entropy
    formula so the temperature and volume ratios reduce to `nR log 2`.

119. **`PhyXMiniProblems/problem_phyx_mini_0477.lean`.** Use back-surface
    imaging and sphere geometry for image distance `2R`, insert this into the
    parallel-ray spherical-refraction equation, and cancel the positive
    radius. Solve `2(n-1)=n` for index `2` and unfold the displayed choice.

120. **`PhyXMiniProblems/problem_phyx_mini_0479.lean`.** Derive the missing
    pressure and the leg works `80`, `0`, and `-40 log 3 J`, sum to
    `40(2-log 3) J`, and multiply by `10 Hz`. Bound `log 3` to prove power
    near `360.56 W`, its 20-watt rounding, and unique choice C.

121. **`PhyXMiniProblems/problem_phyx_mini_0480.lean`.** Normalize the eight
    rectangular-cycle work/heat values, aggregate `W_net = 4*101325` and
    `Q_in = 26*101325`, and cancel the positive common factor for efficiency
    `2/13`. Verify the whole-percent window around displayed `15%`, choice C.

122. **`PhyXMiniProblems/problem_phyx_mini_0481.lean`.** Derive state 1 as
    `200 K`, use the pressure-ratio-five isentropic laws for states 2 and 3,
    and combine compressor/expander works into
    `(15/2)(5^(2/5)-1) J`. Multiply by `60 Hz` and certify `rpow` bounds for
    the exact-power rounding and displayed choice.

123. **`PhyXMiniProblems/problem_phyx_mini_0482.lean`.** Derive all three leg
    works and heats in the positive base scale `E₀`, aggregate the exact net
    work and positive heat input, and cancel `E₀` to obtain
    `(4 log 2 - 2)/(4 log 2 + 3)`. Bound `log 2` for `0.1338` and prove
    unique `13.4%` choice C.

124. **`PhyXMiniProblems/problem_phyx_mini_0484.lean`.** Subtract atmosphere
    from saturation pressure, use circular vent area `pi d²/4`, and solve the
    lift-threshold balance for `9pi/400 kg = 45pi/2 g`. Apply certified `pi`
    bounds to prove `71 g` is uniquely nearest, choice D.

125. **`PhyXMiniProblems/problem_phyx_mini_0485.lean`.** Convert density and
    volume to water mass `5/4 kg`, substitute all masses, heat capacities, and
    temperatures in the isolated calorimetry balance, and solve the initial
    iron temperature as `12535/72 °C`. Rationally prove rounding and strict
    closest choice D.

126. **`PhyXMiniProblems/problem_phyx_mini_0486.lean`.** Compute per-blow
    kinetic-energy loss, multiply by eight, identify all lost energy with nail
    heat, and divide by `0.014*450` to obtain `300/7 K`. Convert the
    temperature rise readout and prove the whole-degree and unique `43 °C`
    choice D predicates.

127. **`PhyXMiniProblems/problem_phyx_mini_0487.lean`.** Add the brick and
    insulation areal resistances to `99/5`, substitute area and boundary
    temperature difference into the steady wall law, and normalize heat loss
    to `11375/33 Btu/h`. Prove it lies in the nearest-50 window for `350` and
    uniquely selects D.

128. **`PhyXMiniProblems/problem_phyx_mini_0489.lean`.** Cancel the common
    positive `4*pi` factor between luminosity and spherical propagation to
    derive `sigma*T^4*(R/D)^2`, using nonzero distance and radius facts before
    clearing denominators. Substitute the rounded solar data, prove the
    irradiance lies within `50 W/m²` of `1100`, and compare with every
    displayed alternative.
