# Prover result: `problem_phyx_mini_0624.lean`

## Completion status

- Closed both proof obligations with no remaining `sorry`.
- `reciprocal_relative_velocities_exact` substitutes the stated Earth-frame fractions into the two Einstein velocity transformations and normalizes the rational expressions to `-15/23` and `15/23`.
- `problem_phyx_mini_0624` derives both absolute speed fractions, proves that `13/20` is within the strict nearest-hundredth tolerance, and rules out choices A, B, and D by exact rational inequalities.
- No theorem signatures, hypotheses, definitions, or imports were changed.
- No redraft is needed.

## Assumption/target split

### Governing laws

- `SatisfiesReciprocalEinsteinVelocityTransformations` states the one-dimensional Einstein transformation in both observer directions. For signed Earth-frame fractions `βa` and `βb`, it uses `(βa - βb) / (1 - βa * βb)` for the velocity of `a` in `b`'s rest frame.
- `HasPhysicalInputParameters` supplies positivity and subluminality of the two Earth-frame inputs, positivity of the SI light-speed readout, and the overtaking order `β_alien < β_enterprise`. It assigns no value to either inter-vessel velocity.

### Previous-part results

- None. The source report has an empty `previous_parts` array, and the blueprint chapter supplies no earlier theorem dependency.

### Figure/data readouts

- `MatchesPrimaryFigure` records the primary raster's ordering Earth–aliens–Enterprise, the visible `Enterprise` label, both leftward green arrows, and the printed annotations `v = 0.60c` and `v = 0.90c`. Drawing coordinates carry ordering only and have no physical distance interpretation.
- `MatchesProblemData` assigns the Earth and vessel rest frames, chooses the positive axis leftward toward Earth, records both vessels moving toward Earth, and gives only the stated Earth-frame fractions `3/5` and `9/10`.
- `displayedRelativeSpeedFraction` independently records choices A–D as `17/20`, `3/4`, `13/20`, and `11/20`. `recordedDatasetAnswer = .C` is source metadata used on the conclusion side, never as a premise.

### Current target conclusions

- `reciprocal_relative_velocities_exact` concludes the signed results `β_alien|Enterprise = -15/23` and `β_Enterprise|alien = 15/23`.
- `problem_phyx_mini_0624` concludes that both speed magnitudes are exactly `15/23 c` and that the independently modeled value uniquely rounds to recorded choice C, `0.65c`.

## Goal-faithfulness audit

`EnterpriseAlienRelativeSpeedSetup.alienVelocityRelativeToEnterprise` and `enterpriseVelocityRelativeToAliens` are independent, signed, dimensionful physical quantities. Neither is defined from `15/23`, `0.65`, choice C, or `recordedDatasetAnswer`.

The data premise contains only the two supplied Earth-frame velocities and qualitative frame/direction assignments. The figure premise contains only raster evidence. The relativity premise contains the unspecialized Einstein transformation in terms of the independent Earth-frame and inter-vessel velocities; it mentions neither the solved fraction nor any answer label. The completed proof substitutes `3/5` and `9/10`, derives the two signs, takes absolute values, and establishes the rounding and uniqueness inequalities.

`MatchesAnswerChoice` is a generic comparison against the complete four-choice table. It does not force any choice to match by unfolding. `recordedDatasetAnswer` is not a hypothesis, and the target value does not occur in any setup field, premise structure, governing-law field, or local definition. Thus no current target conclusion has been smuggled into the assumptions.

## Declarations created and blueprint correspondence

All declarations are in `PhyXMiniProblems.ProblemPhyXMini0624`.

- Dimensionful/readout layer: `SignedVelocityQuantity`, `signedVelocityReadout`, `signedVelocityInMetersPerSecond`, `vacuumLightSpeedInMetersPerSecond`, and `velocityFractionOfLight`.
- Physical and figure vocabulary: `FigureObject`, `VesselLabel`, `InertialFrameLabel`, `HorizontalDirection`, and `EnterpriseRescueFigure`.
- Independent physical model: `EnterpriseAlienRelativeSpeedSetup`.
- Premise families: `MatchesPrimaryFigure`, `MatchesProblemData`, `HasPhysicalInputParameters`, and `SatisfiesReciprocalEinsteinVelocityTransformations`.
- Answer presentation: `relativeVelocityFraction`, `AnswerChoice`, `displayedRelativeSpeedFraction`, `recordedDatasetAnswer`, `RoundsToNearestHundredth`, `MatchesAnswerChoice`, and `IsUniqueMatchingAnswerChoice`.
- Derived lemma: `PhyXMiniProblems.ProblemPhyXMini0624.reciprocal_relative_velocities_exact`.
- Main theorem: `PhyXMiniProblems.ProblemPhyXMini0624.problem_phyx_mini_0624`, corresponding to blueprint label `thm:physics:phyx_mini_0624:target`.

Both proof bodies are now fully proved.

## LeanExplore queries and candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

Queries run:

- `one-dimensional special relativity Einstein velocity transformation relative velocity`
- `DimSpeed speedOfLight dimensionful speed velocity physical units`
- `Dimensionful WithDim LengthUnit TimeUnit speed`
- `TimeUnit seconds UnitChoices SI`

Candidates inspected:

- `Dimensionful` from `Physlib.Units.Basic`: its source defines unit-independent quantities as functions of coherent unit choices satisfying the appropriate scaling law. It is used for signed velocity components.
- `DimSpeed` and `DimSpeed.speedOfLight` from `Physlib.Units.WithDim.Speed`: `DimSpeed` uses a nonnegative carrier, while `speedOfLight` itself has the real-carrier dimensionful type and exact SI value `299792458`; the constant is used directly for normalization.
- `LengthUnit` and the search-grounded `TimeUnit`, `TimeUnit.seconds`, and `UnitChoices.SI`: these ground the SI readout interface.
- `LorentzGroup.toVelocity` from `Physlib.Relativity.LorentzGroup.Restricted.FromBoostRotation`: its source constructs a normalized `Lorentz.Velocity` from a restricted Lorentz transformation. It was inspected but is not a direct API for the problem's signed one-dimensional coordinate-velocity transformation.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`, `UnitChoices.SI`, `LengthUnit`, `LengthUnit.meters`, `TimeUnit`, `TimeUnit.seconds`, `DimSpeed`, and `DimSpeed.speedOfLight`.
- Mathlib/core: `ℝ`, absolute-value notation, exact rational arithmetic, finite inductive types, strings, and real order relations.

## Local abstractions introduced

- `SignedVelocityQuantity` specializes Physlib's unit-independent dimension machinery to a real-valued `length/time` component. It is not a scalar alias: a unit choice is still required before a real readout exists.
- `EnterpriseRescueFigure` preserves the figure's objects, ordering, labels, arrows, colors, and absence of a quantitative position scale separately from physical laws.
- `EnterpriseAlienRelativeSpeedSetup` distinguishes Earth-frame and two reciprocal rest-frame velocity measurements. In particular, the requested quantities remain independent until constrained by relativity.
- `SatisfiesReciprocalEinsteinVelocityTransformations` is the smallest faithful local interface for the collinear coordinate-velocity law because the available Lorentz-velocity API concerns normalized four-velocities rather than this textbook transformation.
- The rounding predicates represent the displayed two-decimal precision; they do not assert the rounded value as an exact physical equality.

## Grounding notes

- LeanExplore found no Mathlib/Physlib declaration directly expressing the reciprocal one-dimensional Einstein coordinate-velocity transformation for dimensionful measurements. A faithful governing-law structure was introduced rather than guessing an API or replacing relativity with Galilean subtraction.
- The requested `.archon/AGENTS.md` is absent in this project state. The available `.archon/prover-modes/physics-formalize.md` and explicit invocation instructions were followed.
- The assigned Lean file contains no `/- USER: ... -/` comments.
- The chapter already maps the target theorem with `\lean{PhyXMiniProblems.ProblemPhyXMini0624.problem_phyx_mini_0624}`. The explicit write-permission block makes the blueprint read-only for this prover, so a blueprint-writing agent should add the appropriate `\leanok` marker.

## Verification

- `archon-lean-lsp` diagnostics report no errors and only unused-variable lints for the frozen hypotheses `hFigure` and `hPhysical`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0624.lean` exited `0` with the same two harmless lints.
- `lean_verify` reports only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`, with no source-scan warnings.
- A direct source scan found no `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide`.
