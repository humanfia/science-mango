# Autoformalization result: `problem_phyx_mini_0740.lean`

## Assumption/target split

### Governing laws

- `SatisfiesIdealProjectileKinematics setup` states uniform no-drag
  projectile motion in coherent SI component readouts. Its horizontal equation
  has constant velocity `v₀ cos θ₀`; its vertical equation is
  `v₀ sin θ₀ t - (1/2) g t²` for every physical elapsed duration.
- `DescribesWallImpact setup` states only the incidence and measurement
  relations: the horizontal displacement at the independently stored impact
  time reaches the wall, and the independently stored impact height is the
  vertical displacement at that event.
- `HasPhysicalProjectileParameters setup` supplies positivity of distance,
  speed, gravity, and impact time, plus the up-and-right trigonometric branch
  shown in the image. These conditions support deriving and cancelling the
  horizontal velocity without assuming a result value.
- `UsesStandardNearEarthGravity setup` supplies the textbook near-Earth
  calibration `g = 49/5 m/s² = 9.8 m/s²`.

### Previous-part results

- None. The source report has an empty `previous_parts` list, and the chapter
  presents a standalone question.

### Figure/data readouts

- `BallWallProjectileSetup` preserves distinct unit-independent physical
  quantities for initial speed, wall distance, gravitational acceleration,
  impact time, and impact height, as well as signed horizontal and vertical
  displacement functions. `launchAngle` uses `Real.Angle` rather than an
  untyped scalar.
- `MatchesPrimaryFigure setup` records the primary raster's thrower, release
  point, ball, rising dotted path, launch ray, `θ₀` arc, horizontal `d` arrow,
  textured ground, and vertical brick wall. Its real coordinates are explicitly
  dimensionless drawing coordinates; the labelled distance remains a physical
  length and the labelled angle remains a `Real.Angle`.
- `MatchesProblemDescription setup` records the printed source data
  `v₀ = 25.0 m/s`, `θ₀ = 40.0°`, and `d = 22.0 m`, together with the stated
  ideal-projectile interpretation.
- `AnswerChoice.displayedHeightInMeters` preserves all printed choices:
  A = 8.0 m, B = 10.0 m, C = 12.0 m, and D = 14.0 m.
- `recordedDatasetAnswer = .C` preserves the supplied metadata only; it is not
  a theorem premise and is not used to select the answer.

### Current target conclusions

- `impactTime_eq_predicted` derives the wall-arrival time
  `d / (v₀ cos θ₀)` from horizontal kinematics and wall incidence.
- `impactHeight_eq_predicted` derives the general wall-impact height by
  substituting that arrival time into vertical kinematics.
- `problem_phyx_mini_0740` concludes that the independent measured impact
  height equals the exact expression computed from the source readouts, lies
  within half a metre of 12.0 m, and makes C the unique closest displayed
  choice.

## Goal-faithfulness audit

The current answer is not present in any hypothesis, law structure, physical
validity structure, figure premise, or setup field. In particular,
`impactTime` and `impactHeightAboveRelease` are stored physical observables;
neither is defined by `predictedImpactTimeInSeconds`,
`predictedImpactHeightInMeters`, `computedImpactHeightInMeters`, or a displayed
choice.

The governing-law structures state motion and incidence relations at arbitrary
times or at the independently named impact event. They contain neither the
eliminated wall-height formula nor the number 12. The exact helper
`computedImpactHeightInMeters` depends only on the printed inputs and the
exposed gravity calibration, while equality of the physical height with that
helper remains a theorem conclusion. Likewise, `MatchesDisplayedHeight` and
`IsUniqueClosestDisplayedHeight` are generic predicates in both height and
choice, so unfolding them cannot establish that C is correct.

Although `recordedDatasetAnswer` records `.C` as source metadata, no theorem
accepts that definition or an equality involving it as evidence. The main
theorem independently concludes the match and unique-closest properties for C.

## Source/law/answer audit

- Source: direct inspection of `740.png` confirms a thrower and release point
  at left, an up-and-right launch segment with a `θ₀` arc, a ball on the rising
  path, a horizontal double arrow labelled `d`, textured ground, and a vertical
  brick wall at right. The image does not display a numerical impact height.
- Law: the chapter relies on the standard uniform-gravity, negligible-drag
  projectile model. LeanExplore exposed no compatible ready-made
  Mathlib/Physlib projectile-trajectory declaration, so the two component laws
  and wall-incidence relations are explicit local proposition structures.
- Answer: with `v₀ = 25 m/s`, `θ₀ = 40°`, `d = 22 m`, and
  `g = 9.8 m/s²`, an independent numerical check gives
  `t_impact ≈ 1.148758414612 s` and `y_impact ≈ 11.993926999700 m`.
  This is within 0.5 m of 12.0 m and is strictly closer to C than to the other
  displayed values, consistent with the recorded answer.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0740:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0740.problem_phyx_mini_0740`.
- Physical dimensions/readouts: `accelerationDimension`, `LengthQuantity`,
  `SignedLengthQuantity`, `TimeQuantity`, `SpeedQuantity`,
  `AccelerationQuantity`, `lengthInMeters`, `signedLengthInMeters`,
  `timeInSeconds`, `speedInMetersPerSecond`, and
  `accelerationInMetersPerSecondSquared`.
- Physical and figure vocabulary: `ProjectileModel`, `FigureObject`,
  `FigureLabel`, `FigureAnchor`, `BallWallFigure`, and
  `BallWallProjectileSetup`.
- Evidence/law interfaces: `MatchesPrimaryFigure`, `degrees`,
  `MatchesProblemDescription`, `UsesStandardNearEarthGravity`,
  `HasPhysicalProjectileParameters`, `SatisfiesIdealProjectileKinematics`, and
  `DescribesWallImpact`.
- Derived expressions and answer representation:
  `predictedImpactTimeInSeconds`, `predictedImpactHeightInMeters`,
  `computedImpactHeightInMeters`, `AnswerChoice`,
  `AnswerChoice.displayedHeightInMeters`, `recordedDatasetAnswer`,
  `MatchesDisplayedHeight`, and `IsUniqueClosestDisplayedHeight`.
- Derived declaration stubs: `impactTime_eq_predicted`,
  `impactHeight_eq_predicted`, and `problem_phyx_mini_0740`.

The blueprint chapter was not edited to add `\leanok`, because this task's
explicit write permissions limit edits to the assigned Lean file and this
result file. A coordinator with blueprint write authority should add the
marker after accepting the formalization.

## LeanExplore queries/candidates actually used

Every query used package filters `Mathlib` and `Physlib`.

- Natural-language query `ideal projectile motion uniform gravity horizontal
  vertical displacement` returned only near misses such as
  `RigidBodyMotion.displacement`, `RigidBodyMotion.velocity`, and a harmonic
  oscillator initial-condition conversion. None states point-particle
  projectile motion under constant downward gravity, so no result was used as
  a governing law.
- Likely-name query `Real.Angle sin cos` selected `Real.Angle.sin`
  (id 146462) and `Real.Angle.cos` (id 146465). Their source, module, and
  docstring were fetched; both are used for launch-velocity components.
- Likely-name query `Real.Angle` selected `Real.Angle` (id 146415), whose
  source/module/docstring were fetched. It is Mathlib's angle modulo `2π` and
  is used for the launch angle and figure label.
- Concept/API query `Dimensionful WithDim SI units speed acceleration`
  selected `UnitChoices.SI` (id 394270), `Dimensionful` (id 394284), and
  `DimSpeed` (id 394481). Source/module/docstring details were fetched for all
  three, and they ground the unit-independent quantities and coherent-SI
  readouts used in the file.
- Likely-name query `DimSpeed` independently confirmed `DimSpeed`
  (id 394481) as the Physlib unit-independent speed type.
- Likely-name query `WithDim` selected `WithDim` (id 394425). Its
  source/module/docstring were fetched and it is used to tag lengths, signed
  displacements, durations, and accelerations with their physical dimensions.
- Likely-name query `DimAcceleration` found no declaration of that name. Its
  results included `WithDim`, `DimSpeed`, a fluid-dynamics material
  acceleration, and unrelated dimension examples; none is a generic
  unit-independent acceleration-magnitude type.

## PhysLean/Mathlib names grounded

- Mathlib: `Real.Angle`, `Real.Angle.sin`, `Real.Angle.cos`, `Real.pi`,
  `NNReal`, and real absolute value/order/arithmetic.
- Physlib: `Dimension`, `L𝓭`, `T𝓭`, `WithDim`, `Dimensionful`,
  `UnitChoices.SI`, and `DimSpeed`.
- Imported grounding modules:
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`,
  `Physlib.Units.WithDim.Basic`, and `Physlib.Units.WithDim.Speed`.

## Local abstractions introduced

- `accelerationDimension` and `AccelerationQuantity` instantiate Physlib's
  genuine `Dimension`/`Dimensionful`/`WithDim` infrastructure at `L T⁻²`
  because the installed library exposes no generic `DimAcceleration` alias.
- `LengthQuantity`, `SignedLengthQuantity`, and `TimeQuantity` are concise
  names built from the same nontransparent unit-independent Physlib quantity
  infrastructure; they are not transparent scalar aliases. Signed component
  displacement is distinguished from nonnegative distance, duration, speed,
  acceleration magnitude, and impact height.
- `ProjectileModel`, `BallWallProjectileSetup`, and the figure vocabulary
  preserve the physical experiment and raster roles that no searched library
  API provides.
- `SatisfiesIdealProjectileKinematics` and `DescribesWallImpact` are the
  smallest local governing-law interfaces that retain the two-dimensional
  uniform-gravity physics and impact event without assuming the requested
  eliminated formula.
- The generic answer-choice predicates preserve the displayed precision and
  closest-choice semantics without embedding which choice wins.

## Grounding gaps and redraft requests

- No directly applicable Mathlib/Physlib declaration was found for ideal
  two-dimensional projectile motion or wall incidence, so faithful local law
  interfaces were required.
- No generic Physlib `DimAcceleration` alias was found. The model therefore
  instantiates the available dimensionful framework explicitly at `L T⁻²`.
- The source does not print a gravitational calibration. The recorded answer
  assumes the conventional textbook value `9.8 m/s²`; a future blueprint
  redraft should state that convention explicitly.
- The requested `.archon/AGENTS.md` is absent. The user-supplied role,
  `.archon/prover-modes/physics-formalize.md`, `.archon/PROGRESS.md`, the
  blueprint, source report, and primary image supplied the available context.
- The assigned file's `/- USER: ... -/` comment says it did not exist when the
  original autoformalization began; it existed for this retry and contained no
  additional file-specific modeling hint.
- The `archon` executable was not available on `PATH`, so the optional DAG
  navigation command could not be run. The source report independently shows
  no previous-part dependencies.

## Verification

- The project Lean language server reports no errors or failed dependencies,
  only the three deliberate `sorry` warnings for `impactTime_eq_predicted`,
  `impactHeight_eq_predicted`, and `problem_phyx_mini_0740`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0740.lean` exited
  successfully and emitted only those same three expected warnings.
