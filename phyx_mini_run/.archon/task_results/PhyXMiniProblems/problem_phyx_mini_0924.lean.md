# Autoformalization result: `problem_phyx_mini_0924.lean`

## Status

Complete for Archon iteration 002 of the `physics-formalize` stage. The retry
gate's exact reason was missing post-formalization evidence, not a defect in
the physical statement. I therefore re-audited the Lean model against the
source report, blueprint, and primary raster, reran LeanExplore grounding,
and retained the faithful declaration signatures. The assigned Lean file
compiles with four expected `declaration uses sorry` warnings and no errors.

## Assumption/target split

### Governing laws

- `SatisfiesFiniteDoubleSlitPhaseLaws.fullPathPhaseDifference` states the
  general full inter-slit path-phase law
  `β(θ) = 2π (d/λ) sin θ` on the forward angular branch and in every common
  length unit.
- `SatisfiesFiniteDoubleSlitPhaseLaws.singleSlitDiffractionPhase` states the
  general finite-slit envelope phase law
  `α(θ) = π (a/λ) sin θ`.
- `IsInterferenceMinimum` and `IsInterferenceMaximum` characterize the
  destructive and constructive two-source fringes by odd and even multiples
  of `π`, respectively. These are all-order definitions, not assumptions
  about a selected order.
- `IsDiffractionMinimum` characterizes a noncentral single-slit minimum by
  `α = nπ`, with positive natural order.
- `NoInterferenceMaximumEliminatedByDiffraction` faithfully records the
  problem's explicit assumption that no constructive interference angle is
  also a diffraction-envelope minimum.

### Previous-part results

- None. The source report has an empty `previous_parts` list, and no earlier
  declaration is assumed.

### Figure/data readouts

- `MatchesProblemWavelengthReadout` records the stated physical wavelength as
  `435 nm` through a dimensionful Physlib length quantity.
- `MatchesPrimaryBetaVersusSineFigure` records the primary raster's horizontal
  axis `sin θ`, vertical axis `β (rad)`, ticks `0`, `0.5`, and `1`, the `βₛ`
  top-scale label, four-by-four rectangular grid, and thick black straight
  trace from the origin to the top-right corner.
- The same predicate records the prose calibration `βₛ = 80.0 rad`, the
  straight-line readout `β = 80 sin θ`, and the connection between the plot
  ordinate and the independent physical `betaRadiansAt` observable.
- `displayedAngleInDegrees` transcribes all four choices: `77.5`, `80.0`,
  `79.0`, and `75.0` degrees. `recordedDatasetAnswer` separately transcribes
  source metadata label C; it is not a theorem premise.

### Current target conclusions

- `slitCenterSeparationInNanometers_eq` derives the intermediate slit spacing
  `80 * 435 / (2π) nm`, preserving the wavelength's role in the model.
- `twentyFivePi_is_largest_visible_odd_phase` derives that `25π` is the
  greatest odd phase multiple below the graph ceiling `80 rad`.
- `greatestInterferenceMinimumAngle_exact` derives that the greatest forward
  interference minimum is `arcsin(25π/80)` radians.
- `problem_phyx_mini_0924` concludes both that exact greatest-angle property
  and that its degree readout uniquely matches displayed choice C to the
  nearest tenth of a degree.

## Goal-faithfulness audit

The exact angle `arcsin(25π/80)`, the order `12`/phase `25π`, and the
choice-matching conclusion occur only in derived lemma or theorem
conclusions. They do not occur in `FiniteDoubleSlitSetup`, any source-readout
predicate, either governing-law field, or the non-elimination premise.

`betaRadiansAt` and `alphaRadiansAt` are independent phase observables. They
are not defined from the desired angle. Likewise, slit separation and slit
width are independent dimensionful physical lengths rather than scalar
aliases or values chosen to force answer C. The figure legitimately supplies
the entire straight trace `β = 80 sin θ`; determining which odd phase is the
last reachable one and inverting the sine remain conclusion-side work.

The answer table is presentation data only. Although
`recordedDatasetAnswer` transcribes C as metadata, the main theorem does not
derive C by unfolding that definition: it requires
`IsUniqueMatchingDisplayedAngle ... .C`, which compares the exact physical
angle against all four displayed values. No premise asserts any match or
selects a choice.

No `True`, reflexive target, axiom, `admit`, `native_decide`, scalar alias for
a physical length, or definition-unfolding shortcut was introduced.

## Declarations created and blueprint alignment

- Physical quantity/readout layer: `LengthQuantity`, `lengthReadout`,
  `lengthInNanometers`, and `angleInDegrees`.
- Figure vocabulary: `FigureAxis`, `FigureAxisUnit`, `VerticalScaleLabel`,
  `TraceStyle`, and `BetaVersusSineFigure`.
- Physical model: `FiniteDoubleSlitSetup`, `IsForwardAngle`,
  `HasPhysicalDoubleSlitParameters`, `MatchesProblemWavelengthReadout`,
  `MatchesPrimaryBetaVersusSineFigure`, and
  `SatisfiesFiniteDoubleSlitPhaseLaws`.
- Fringe and source-assumption vocabulary: `IsInterferenceMinimum`,
  `IsInterferenceMaximum`, `IsDiffractionMinimum`,
  `NoInterferenceMaximumEliminatedByDiffraction`, and
  `IsGreatestInterferenceMinimum`.
- Answer vocabulary: `AnswerChoice`, `displayedAngleInDegrees`,
  `recordedDatasetAnswer`, `MatchesDisplayedTenthDegree`, and
  `IsUniqueMatchingDisplayedAngle`.
- Derived declarations: `slitCenterSeparationInNanometers_eq`,
  `twentyFivePi_is_largest_visible_odd_phase`, and
  `greatestInterferenceMinimumAngle_exact`.
- Blueprint label `thm:physics:phyx_mini_0924:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0924.problem_phyx_mini_0924`.

The explicit write restrictions permit edits only to the assigned Lean file
and this result report, so the blueprint chapter was not edited. The
coordinating agent should add `\leanok` to the target environment after
accepting this formalization.

## LeanExplore queries and candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

Queries issued:

- `finite double slit interference phase difference destructive minima single slit diffraction`
- `Dimensionful WithDim physical length nanometers UnitChoices SI`
- `Real.arcsin inverse sine radians degrees`
- `WithDim`
- `Dimension.L𝓭 physical length dimension`

Candidates whose source/module information was fetched and used:

- `LengthUnit.nanometers` from
  `Physlib.SpaceAndTime.Space.LengthUnit`, confirmed as `10⁻⁹ m`.
- `Dimensionful` from `Physlib.Units.Basic`, used for unit-independent
  physical quantities.
- `WithDim` from `Physlib.Units.WithDim.Basic`, used with the length dimension
  rather than wrapping a bare scalar.
- `Dimension.L𝓭` from `Physlib.Units.Dimension`, used as the physical length
  dimension.
- `UnitChoices.SI` from `Physlib.Units.Basic`, used as the coherent base whose
  length component is replaced for nanometre readouts.
- `Real.arcsin` from
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse`, confirmed from
  its source as the inverse-sine function with values in the principal range
  `[-π/2, π/2]`, as required by the forward-angle target.

The optics search returned no two-slit/diffraction apparatus. Its leading
results were unrelated `Complex.slitPlane` and generic finite-set minimum
declarations; those near misses were not used.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `LengthUnit`,
  `LengthUnit.nanometers`, and `UnitChoices.SI`.
- Mathlib: `Real.sin`, `Real.arcsin`, `Real.pi`, real absolute value, and the
  standard ordered-real operations used to define the forward branch,
  greatest angle, and display tolerance.

## Local abstractions introduced

- `FiniteDoubleSlitSetup` is the smallest local physical interface retaining
  wavelength, slit-center separation, common slit width, the distinct
  inter-slit and single-slit phase observables, and the graph. Its length
  fields use Physlib dimensional infrastructure.
- `BetaVersusSineFigure` preserves the literal axes, units, labels, grid,
  line style, scale, and plotted readout from the primary image.
- `SatisfiesFiniteDoubleSlitPhaseLaws` is local because no matching
  Mathlib/Physlib finite-double-slit API was found. It states the standard
  general phase laws and contains no requested numerical angle.
- Forward angles are represented by radian-valued reals because ordering is
  essential to “greatest” and angle/phase is dimensionless. Degree values are
  explicit readouts only.

## Grounding gaps

- LeanExplore found general plane-wave and trigonometric infrastructure but no
  ready-made two-slit interference, finite-aperture diffraction, labelled
  `β`-versus-`sin θ` graph, or missing-maximum API. The faithful local
  abstractions above fill that gap.
- The source does not explicitly define its `β` convention. The recorded
  `79.0°` answer determines that `β` is the full path phase difference, with
  minima at odd multiples of `π`; the alternative half-phase convention
  would yield about `74.2°` and would not match the supplied answers. This
  convention is stated explicitly in the Lean documentation and governing
  law.
- `.archon/AGENTS.md` is absent from this checkout. The available
  `.archon/PROGRESS.md` and complete
  `.archon/prover-modes/physics-formalize.md` were read and followed.
- The prompt-advertised `archon` executable is not on the actual shell
  `PATH`, but invoking the copy under the parent `.venv/bin` directly showed
  that `thm:physics:phyx_mini_0924:target` has dependency count zero and no
  ancestors. This agrees with the source report's empty `previous_parts`.

## Verification

- `archon-lean-lsp` diagnostics and outline: both imports and all declarations
  elaborate; diagnostics contain four expected `declaration uses sorry`
  warnings and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0924.lean`: exit code 0
  with the same four expected warnings.
- A trailing-whitespace scan passed.
- Source scan found exactly the four required `sorry` bodies and no `axiom`,
  `admit`, or `native_decide`.

## Redraft requests

- The blueprint proof is only a generic autoformalization directive. A later
  plan/review pass should record the substantive calculation: the largest odd
  multiple below `80` is `25π`, so
  `θ = arcsin(25π/80) ≈ 79.036°`, which rounds to `79.0°`.
