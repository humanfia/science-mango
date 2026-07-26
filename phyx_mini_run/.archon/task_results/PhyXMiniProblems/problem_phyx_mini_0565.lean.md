# Autoformalization result: `problem_phyx_mini_0565.lean`

The assigned file compiles under
`lake env lean PhyXMiniProblems/problem_phyx_mini_0565.lean` with exactly two
expected `declaration uses sorry` warnings and no errors.

## Assumption/target split

### Governing laws

- `Lorentz.Velocity 2` supplies the physical rocket four-velocity in each
  frame; Physlib's type enforces unit Minkowski norm and future direction.
- `SatisfiesPlanarVelocityGeometry` states the polar decomposition of the
  rocket velocity measured by `O` into x- and y-components using the measured
  speed and direction angle.
- `SatisfiesLorentzBoostVelocityLaw` states that the independently supplied
  rocket four-velocity measured by `O'` is the result of applying
  `LorentzGroup.boost` along the x-axis to the four-velocity measured by `O`.
- `HasPhysicalInputParameters` records positivity/nonnegativity and
  subluminality domain conditions. In particular, its frame-speed bound is
  the proof parameter required by `LorentzGroup.boost`.

### Previous-part results

- None. This is a standalone multiple-choice problem.

### Figure/data readouts

- `MatchesObliqueRocketScenario` records that the initial observer is `O`, the
  requested observer is `O'`, and `O'` moves in the positive common x
  direction.
- `MatchesProblemReadouts` records only the given data: rocket speed `0.60 c`
  in `O`, rocket direction `45°` in `O`, and frame speed `0.80 c`.
- `MatchesSuppliedTwoRocketFigure` records the actual raster labels
  (`O_earth`, `O_A`, `O_A`, `O_B`, rockets `A` and `B`, coordinate labels),
  the directions of `V_A`, `V_B`, and `V_AB`, the displayed common-axis
  relation, and the absence of a calibrated quantitative scale.
- `displayedSpeedFraction` records the four answer-choice coefficients
  `0.55`, `0.69`, `0.95`, and `10.2`; `recordedDatasetAnswer` records the
  source metadata value `B`, but it is not a theorem hypothesis.

### Current target conclusions

- `rocket_speed_fraction_in_OPrime_exact` concludes that the speed read from
  the independently modeled `O'` four-velocity equals the closed expression
  obtained from the given `0.60`, `45°`, and `0.80` inputs.
- `problem_phyx_mini_0565` concludes both that exact equality and that choice
  `B` is the unique displayed value within the nearest-hundredth tolerance.
  Thus the target represents the recorded answer `0.69 c` as a rounding, not
  as a false exact equality.

## Goal-faithfulness audit

- The requested `O'` four-velocity is an independent field of
  `ObliqueRocketBoostSetup`; it is not defined to be the expected answer.
- `MatchesProblemReadouts` mentions only the input velocity in `O`, the input
  angle, and the observer-frame speed. It contains neither the transformed
  speed nor choice `B`.
- The boost predicate contains the standard governing frame-change relation,
  not the requested scalar answer. Recovering the target speed still requires
  taking component/time ratios, forming the Euclidean magnitude, and doing
  the numerical rounding argument.
- `expectedRocketSpeedFractionInOPrime` is constructed solely from the three
  given input readouts and the standard longitudinal/transverse boost
  expression. Its equality with the independent `O'` speed remains a lemma
  conclusion.
- `recordedDatasetAnswer` is metadata used on the conclusion side. No premise
  asserts that it matches, much less uniquely matches, the modeled speed.
- The raster predicates contain only qualitative labels and arrows. They do
  not encode the numerical target.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0565:target` corresponds to theorem
  `PhyXMiniProblems.ProblemPhyXMini0565.problem_phyx_mini_0565`.
- Helper lemma
  `PhyXMiniProblems.ProblemPhyXMini0565.rocket_speed_fraction_in_OPrime_exact`
  isolates the exact relativistic transformation result used by the final
  multiple-choice theorem.
- Supporting declarations cover named planar axes, inertial-frame roles,
  typed four-velocity scalar readouts, the auxiliary raster vocabulary,
  scenario/data/physics predicates, exact expected value, displayed choices,
  and nearest-hundredth matching.

## LeanExplore queries and candidates used

All searches used package filters `['Mathlib', 'Physlib']`.

- Query `special relativistic velocity transformation Lorentz boost
  four-velocity` returned and motivated use of `LorentzGroup.boost`
  (LeanExplore id 391171) and `Lorentz.Velocity` (id 392568).
- Query `Lorentz.Velocity LorentzGroup.boost` confirmed those same intended
  Physlib declarations rather than a local scalar model.
- Query `Lorentz.Vector.spatialPart Lorentz.Vector.timeComponent` returned the
  component projections `Lorentz.Vector.spatialPart` (id 392334) and
  `Lorentz.Vector.timeComponent` (id 392342), which are used to define the
  three-velocity component readout.
- Query `Real.Angle cos sin angle` returned `Real.Angle.sin` (id 146462) and
  `Real.Angle.cos` (id 146465), used in the polar input geometry and exact
  expected expression.
- Source, module, and docstring information was fetched for precisely those
  six declarations before they were used.

## Physlib/Mathlib names grounded

- `Lorentz.Velocity` from
  `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic`.
- `LorentzGroup.boost` from
  `Physlib.Relativity.LorentzGroup.Boosts.Basic`, made available together with
  its action by `Physlib.Relativity.LorentzGroup.Boosts.Apply`.
- `Lorentz.Vector.spatialPart` and `Lorentz.Vector.timeComponent` from
  `Physlib.Relativity.Tensors.RealTensor.Vector.Basic`.
- `Real.Angle`, `Real.Angle.sin`, `Real.Angle.cos`, `Real.pi`, `Real.sqrt`,
  finite sums, and real absolute value from Mathlib.

## Local abstractions introduced

- `PlanarAxis`, `InertialFrameLabel`, and `AxisDirection` retain the semantic
  roles of coordinates, observers, and direction rather than replacing
  physical velocities with bare real aliases.
- `ObliqueRocketBoostSetup` stores actual Physlib four-velocities. Real values
  in the file are explicitly scalar fractions of `c`, angles, or displayed
  numerical readouts.
- `TwoRocketAuxiliaryFigure` and its label enumerations preserve the primary
  raster evidence without pretending that the schematic drawing has a
  calibrated velocity scale.
- Local scenario/law predicates were introduced to separate source readouts,
  physical domain conditions, planar geometry, and the Lorentz frame-change
  law from the theorem conclusions.

## Grounding gaps and redraft requests

- LeanExplore did not expose a single ready-made theorem for the full oblique
  two-dimensional three-velocity transformation and its numerical magnitude.
  The formalization therefore uses the grounded Physlib four-velocity and
  boost primitives plus faithful local component readouts and law interfaces.
- The primary raster shows a collinear two-rocket scenario, while the prose
  asks about one obliquely moving rocket and a boosted observer. The file
  explicitly keeps the raster as auxiliary qualitative evidence and bases the
  numerical law on the prose data. A future blueprint revision could clarify
  whether this image was intentionally paired with the problem.
- The documented `archon dag-query` navigation command was unavailable in the
  runtime (`archon: command not found`), so no dependency-graph declarations
  were imported.
- The required `.archon/AGENTS.md` was absent; the available and applicable
  `.archon/prover-modes/physics-formalize.md` was read and followed.
- The blueprint environment was not edited to add `\leanok` because the task's
  explicit write permissions allow edits only to the assigned Lean file and
  this result file. The orchestration/blueprint-maintenance stage should add
  `\leanok` to `thm:physics:phyx_mini_0565:target` after accepting this result.
