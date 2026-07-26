# Prover result: `problem_phyx_mini_0402.lean`

## Status

Complete. The sole proof obligation,
`work_done_on_gas_is_sixty_joules`, is closed without changing its signature.

## Proof summary

- Rewrote the total physical work readout using
  `total_work_is_sum_of_segment_works`.
- Specialized `segment_work_law` to `initialToPeak` and `peakToFinal`.
- Used `state_readouts_match_figure_coordinates` and the six exact coordinate
  fields to substitute `(300 cm³, 200 kPa)`, `(200 cm³, 400 kPa)`, and
  `(100 cm³, 200 kPa)`.
- Unfolded the straight-segment formula and the `1 / 1000` conversion; exact
  normalization gives `30 J + 30 J = 60 J`.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0402.lean` succeeds.
- The configured root `lake build` succeeds (4 jobs).
- Lean LSP diagnostics contain no errors. The only diagnostic is an
  unused-variable warning for the frozen qualitative hypothesis `h_scenario`;
  the quantitative figure calibration and governing work law suffice.
- The theorem axiom audit reports only Lean's standard `propext`,
  `Classical.choice`, and `Quot.sound`, with no source-scan warnings.
- A source scan finds no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide` in the assigned file.
- `git diff --check` reports no whitespace errors.
- The standalone Lake target
  `PhyXMiniProblems.problem_phyx_mini_0402` is not configured, so it reports
  `unknown target`; direct per-file Lean compilation is the relevant check.

## Blueprint readiness

`work_done_on_gas_is_sixty_joules` is ready for deterministic `\leanok`
synchronization. The blueprint was not edited because prover permissions
reserve marker changes for the synchronization phase.

## Redraft needed

None.

---

# Prior autoformalization result: `problem_phyx_mini_0402.lean`

## Retry resolution

- Archon iteration: `003` (final formalization review retry).
- The current gate reason is: "No genuine post-formalization task result exists
  for retry target 0402. The only current evidence is the generic
  physics-grounding preflight, which predates the revised Lean model and cannot
  establish the queries/candidates actually used, grounded Mathlib/Physlib
  names, introduced local abstractions, grounding gaps, or source/law/answer
  split; missing evidence is a failed review."
- This is an evidence-only rejection. A fresh audit of the revised Lean file,
  source report, blueprint, and primary raster found no semantic defect, so the
  physical statement and protected target signature were preserved unchanged.
  No public declaration was added, removed, or renamed in this iteration.
- The chapter contains `% archon:physics`; the `physics-formalize` discipline
  therefore applies. The requested `.archon/AGENTS.md` is absent, so the
  available `.archon/prover-modes/physics-formalize.md` role specification was
  used together with `.archon/PROGRESS.md`.

## Assumption/target split

### Governing laws

- `straightSegmentWorkOnGasInJoules` states the generic straight-leg
  trapezoidal rule: average endpoint pressure times the volume decrease,
  multiplied by `joulesPerKilopascalCubicCentimeter = 1 / 1000`.
- `ObeysPiecewiseLinearPressureVolumeWorkLaw.segment_work_law` relates each
  independent physical leg-work field to that generic rule.
- `ObeysPiecewiseLinearPressureVolumeWorkLaw.total_work_is_sum_of_segment_works`
  states that the total physical work readout is the sum of the two leg-work
  readouts.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- The primary raster, rather than the approximate auxiliary caption, fixes
  `i = (300 cm³, 200 kPa)`, the unlabelled peak at
  `(200 cm³, 400 kPa)`, and `f = (100 cm³, 200 kPa)`.
- `MatchesPrimaryPressureVolumeFigure` records the pressure/volume axis roles,
  printed `kPa` and `cm³` units, all three coordinates, visible endpoint labels
  `i` and `f`, the unlabelled peak, both straight segments, and the arrow order
  `i → peak → f`.
- Its `state_readouts_match_figure_coordinates` field calibrates the scalar
  plot coordinates against the independent physical `GasVolume` and
  `DimPressure` states.
- `MatchesTwoStageCompressionScenario` records that both legs are
  compressions, with pressure rising on the first and falling on the second.

### Current target conclusion

- `work_done_on_gas_is_sixty_joules` concludes only on the target side that
  `energyInJoules process.workDoneOnGas = 60`.

## Goal-faithfulness audit

- The independent fields `workDoneOnGasOnSegment` and `workDoneOnGas` have
  physical type `DimEnergy`; neither is defined to equal the requested answer.
- No scenario or figure predicate contains `60`, a total-work value, or an
  answer-choice assertion.
- The governing-law predicate contains only the generic straight-segment
  pressure-volume law and the generic additivity law. Substituting the primary
  figure coordinates is still required to derive the target.
- The `60 J` result is not proved by unfolding a target-specific definition.
  Each leg contributes `30 J`, and their sum is the theorem's substantive
  conclusion.
- Real numbers represent only named SI/figure readouts, conversion factors,
  diagram coordinates, and the final displayed answer. Pressure, volume, and
  work themselves remain dimensionful quantities.

## Declarations and blueprint labels

The evidence-only retry retained the following existing declaration topology;
there were no additions or removals:

- `GasVolume` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-gasvolume`
- `volumeInCubicCentimeters` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-volumeincubiccentimeters`
- `pressureInPascals` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-pressureinpascals`
- `pressureInKilopascals` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-pressureinkilopascals`
- `energyInJoules` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-energyinjoules`
- `joulesPerKilopascalCubicCentimeter` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-joulesperkilopascalcubiccentimeter`
- `straightSegmentWorkOnGasInJoules` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-straightsegmentworkongasinjoules`
- `DiagramPoint` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-diagrampoint`
- `ProcessSegment` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-processsegment`
- `ProcessSegment.initialPoint` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-processsegment-initialpoint`
- `ProcessSegment.finalPoint` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-processsegment-finalpoint`
- `AxisQuantity` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-axisquantity`
- `VolumeAxisUnit` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-volumeaxisunit`
- `PressureAxisUnit` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-pressureaxisunit`
- `SegmentShape` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-segmentshape`
- `ProcessKind` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-processkind`
- `PressureTrend` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-pressuretrend`
- `ThermodynamicState` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-thermodynamicstate`
- `PressureVolumeFigure` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-pressurevolumefigure`
- `TwoStageGasCompression` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-twostagegascompression`
- `MatchesTwoStageCompressionScenario` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-matchestwostagecompressionscenario`
- `MatchesPrimaryPressureVolumeFigure` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-matchesprimarypressurevolumefigure`
- `ObeysPiecewiseLinearPressureVolumeWorkLaw` —
  `def:physics:phyx-mini-0402:phyxminiproblems-problemphyxmini0402-obeyspiecewiselinearpressurevolumeworklaw`
- `work_done_on_gas_is_sixty_joules` —
  `thm:physics:phyx_mini_0402:target`.

The blueprint was not edited because the final write-permission block permits
changes only to the assigned Lean file and this result file. The plan agent or
dispatcher should add `\leanok` to the target environment.

## LeanExplore queries/candidates actually used

All searches in this iteration passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query
  `dimensionful physical pressure energy volume SI units thermodynamic work`
  returned and grounded `UnitChoices.SI`, `DimPressure`,
  `DimPressure.pascal`, `Dimensionful`, and `DimEnergy.joule`. Near misses
  `NVEHamiltonian.pressure` and `IdealGas.ideal_gas_law` describe an ensemble
  pressure and the ideal-gas equation, not work along a plotted path.
- Likely-name query
  `DimPressure DimEnergy Dimensionful UnitChoices.SI pascal joule` confirmed
  the dimensional carriers and named SI units actually used.
- Natural-language query
  `thermodynamic work pressure volume integral straight line process` returned
  generic Mathlib `curveIntegral` and `curveIntegral_segment` plus
  `NVEHamiltonian.pressure`, but no ready-made thermodynamic straight-line
  `p dV` work law compatible with the figure data.
- Natural-language query
  `physical volume dimension length cubed Dimensionful WithDim` returned
  `Dimensionful`, `Dimension.L𝓭`, and `WithDim`, which are used to build the
  nonnegative dimension-`L³` volume carrier.
- Likely-name query
  `DimVolume cubic centimeter DimPressure.kilopascal kilopascal kPa` returned
  `DimPressure`, `Dimension`, `WithDim`, and `DimEnergy`, but no `DimVolume`,
  cubic-centimetre unit, or kilopascal unit.
- Current source text and module metadata were fetched only for the eight
  declarations actually used: `Dimensionful` (id 394284), `WithDim` (394425),
  `Dimension.L𝓭` (394324), `UnitChoices.SI` (394270), `DimPressure`
  (394474), `DimPressure.pascal` (394475), `DimEnergy` (394468), and
  `DimEnergy.joule` (394469).

## Physlib/Mathlib names grounded

- `Dimensionful` and `UnitChoices.SI` — `Physlib.Units.Basic`
- `WithDim` — `Physlib.Units.WithDim.Basic`
- `Dimension.L𝓭` — `Physlib.Units.Dimension`
- `DimPressure` and `DimPressure.pascal` —
  `Physlib.Units.WithDim.Pressure`
- `DimEnergy` and `DimEnergy.joule` — `Physlib.Units.WithDim.Energy`
- Mathlib supplies `NNReal` and `ℝ`; their compatibility with the fetched
  Physlib signatures was verified by LSP elaboration and the real Lake compile.

The file directly imports `Mathlib`, `Physlib.Units.WithDim.Energy`, and
`Physlib.Units.WithDim.Pressure`.

## Local abstractions introduced

- `GasVolume` uses Physlib's generic `Dimensionful (WithDim ... NNReal)` with
  dimension `L³`. This preserves both physical dimension and nonnegativity;
  it is not a scalar alias.
- `volumeInCubicCentimeters`, `pressureInPascals`,
  `pressureInKilopascals`, and `energyInJoules` are explicitly named scalar
  projections from physical quantities. The conversion constant and
  `straightSegmentWorkOnGasInJoules` operate only on these labelled readouts.
- `DiagramPoint` and `ProcessSegment`, together with `initialPoint` and
  `finalPoint`, preserve the three figure locations and the two directed legs.
  `AxisQuantity`, the two axis-unit types, `SegmentShape`, `ProcessKind`, and
  `PressureTrend` preserve the nonnumeric annotations visible in the image and
  stated in the scenario.
- `ThermodynamicState` pairs dimensionful volume and pressure;
  `TwoStageGasCompression` keeps those states, the abstract gas, physical
  segment/total works, and the figure as independent data.
- The gas sample is an abstract theorem/structure parameter `GasSample : Type`
  and is stored independently in `TwoStageGasCompression`. This is the
  smallest abstraction needed for the unspecified working gas and does not
  identify a gas with a scalar.
- `PressureVolumeFigure` preserves the literal axis roles, printed units,
  points, labels, segments, and arrows from the image.
- `MatchesTwoStageCompressionScenario` and
  `MatchesPrimaryPressureVolumeFigure` separate prose/figure evidence from the
  work conclusion. `ObeysPiecewiseLinearPressureVolumeWorkLaw` is the smallest
  local interface for the unavailable thermodynamic law: it states generic
  per-leg work and additivity without assigning the requested numeric answer.

## Grounding gaps

- No ready-made Physlib volume type, cubic-centimetre unit, kilopascal unit, or
  thermodynamic straight-line `p dV` work theorem was found. The local
  abstractions above retain the missing physical roles explicitly.
- `.archon/AGENTS.md`, requested by the task header, is absent from the project;
  `.archon/prover-modes/physics-formalize.md` was read as the available role
  specification.
- The `archon` executable was not available on `PATH`, so the optional DAG
  navigation commands could not be used.
- No Lean redraft is requested: the gate reason is evidence-only and the
  source/law/answer audit found the current statement faithful.

## Source/law/answer audit

- The primary image, not the approximate auxiliary caption, visibly places
  `i`, the peak, and `f` on the exact axis ticks `(300, 200)`, `(200, 400)`,
  and `(100, 200)` in `(cm³, kPa)` coordinates. Its arrows run
  `i → peak → f`, so both legs are compressions.
- With work on the gas defined as average pressure times volume decrease, each
  straight leg contributes
  `((200 + 400) / 2) * (100 cm³) * 10⁻³ = 30 J`.
  Additivity therefore supports the recorded choice C, `60 J`.
- The governing-law predicate states only the generic per-leg trapezoidal law
  and total-work additivity. It does not mention `60` or specialize itself to
  the plotted coordinates.

## Verification

- Fresh `archon-lean-lsp` diagnostics reported only `declaration uses sorry`
  at the target theorem (line 265); the file outline confirmed all imports and
  the target signature.
- Fresh LSP local searches verified `Dimensionful`, `WithDim`, `DimPressure`,
  and `DimEnergy`; LeanExplore source retrieval verified the namespace-qualified
  unit and dimension declarations that local prefix search did not return.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0402.lean` exited with code
  0 in this iteration and emitted only the intentional `sorry` warning.
- No `/- USER: ... -/` file-specific hint is present in the assigned Lean file.
