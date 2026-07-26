# Autoformalization result: `problem_phyx_mini_0156.lean`

## Assumption/target split

### Governing laws

- `HasConstantReadoutRates` states that the source-position readout has the
  stated constant speed as its derivative and that the rod-temperature
  readout has the unknown constant temperature rate as its derivative.
- `ObeysLinearThermalExpansionRateLaw` states the one-dimensional governing
  relation `v = alpha * d * dT/dt` in compatible SI readouts.
- `UsesAluminumExpansionCalibration` supplies the independent material
  property `alpha = 23 * 10^-6 K^-1` for aluminum. It does not supply the
  requested temperature rate.

### Previous-part results

- None. The source report's `previous_parts` array is empty, and no dependency
  theorem is required.

### Figure/data readouts

- `HasStatedLengthAndSpeed` records the two problem data: effective heated
  length `d = 2.00 cm` and source speed magnitude `100 nm/s`.
- `MatchesProblemDescription` records the aluminum material, fixed clamp,
  rate-controlled heater, and the clamp-to-source positive axis.
- `MatchesNarratedRodDiagram` records the auxiliary caption's labeled layout:
  radioactive source at the left/source end, electric heater at the central
  section, and clamp at the right/clamp end.
- `RecordsProvidedFigureMismatch` separately records what is actually visible
  in `phyx_data/test_image/156.png`: a laser/prism scene with `30 degree`,
  `60 degree`, and `22.6 degree` labels. It also records that the auxiliary
  caption describes a heated-rod scene and that the chapter declares the image
  primary. These unrelated optical readouts do not enter the thermal law.
- `answerTemperatureRateKelvinPerSecond` neutrally transcribes all four listed
  answers: `0.195`, `0.204`, `0.212`, and `0.217 K/s`.

### Current target conclusions

- `stated_length_and_speed_in_si` derives the intermediate unit conversions
  `2 cm = 1/50 m` and `100 nm/s = 1/10000000 m/s`.
- `problem_phyx_mini_0156` concludes that the required rate is exactly
  `5/23 K/s` and that this physical rate matches choice D to the nearest
  `0.001 K/s`.

## Goal-faithfulness audit

The requested exact rate `5/23 K/s` and the assertion that choice D matches it
occur only in the conclusion of `problem_phyx_mini_0156`. They do not occur in
`ThermalExpansionSetup`, any data predicate, the material-calibration
predicate, either constant-rate derivative premise, or the governing-law
predicate. `temperatureRate` is an unconstrained dimensionful field until the
independent data and expansion law are supplied.

The governing law is the general physical relation `v = alpha d (dT/dt)`, not
the solved numeric answer. `answerTemperatureRateKelvinPerSecond` lists every
candidate uniformly, and `MatchesAnswerToNearestThousandthKelvinPerSecond` is a
generic tolerance relation. `recordedAnswerChoice` is metadata and is not a
theorem premise.

The provided laser/prism image is modeled as provenance rather than silently
treated as a rod diagram or used to prove a thermal conclusion. Its angle
readouts are absent from the expansion law. Conversely, the source/heater/
clamp layout is explicitly attributed to the narrated diagram.

Lengths, positions, times, temperatures, rates, the expansion coefficient,
and speed are not scalar aliases. They use Physlib dimensions through
`Dimensionful (WithDim ... )` or the supplied `DimSpeed`; real numbers are
introduced only by unit-explicit readout functions.

## Declarations created and blueprint labels

- Dimensionful types: `LengthQuantity`, `SignedLengthQuantity`,
  `TimeQuantity`, `TemperatureQuantity`, `TemperatureRateQuantity`,
  `LinearExpansionCoefficientQuantity`, and `SpeedQuantity`.
- Unit readouts/conversion: `lengthReadout`, `signedLengthReadout`,
  `speedReadout`, `temperatureReadout`, `temperatureRateReadout`,
  `expansionCoefficientReadout`, their named SI/problem-unit specializations,
  and `timeOfSeconds`.
- Physical and figure roles: `RodMaterial`, `RodComponent`, `RodRegion`,
  `ClampCondition`, `HeaterControl`, `RodAxisOrientation`, `FigureScene`,
  `FigureEvidencePolicy`, and `PrimaryImageAngle`.
- Setup/data/law interfaces: `ThermalExpansionSetup`,
  `MatchesProblemDescription`, `MatchesNarratedRodDiagram`,
  `RecordsProvidedFigureMismatch`, `HasStatedLengthAndSpeed`,
  `UsesAluminumExpansionCalibration`, `HasConstantReadoutRates`, and
  `ObeysLinearThermalExpansionRateLaw`.
- Answer model: `AnswerChoice`, `answerTemperatureRateKelvinPerSecond`,
  `recordedAnswerChoice`, and
  `MatchesAnswerToNearestThousandthKelvinPerSecond`.
- Supporting result: `stated_length_and_speed_in_si`.
- Blueprint label `thm:physics:phyx_mini_0156:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0156.problem_phyx_mini_0156`.

## LeanExplore queries/candidates actually used

Every query used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `linear thermal expansion length change coefficient
  temperature change` found Physlib's dimension infrastructure
  `Dimension.L𝓭`, `Dimension.Θ𝓭`, and `LengthUnit`, but no dedicated linear
  thermal-expansion law.
- Natural-language query `physical dimensions units length time temperature
  quantity` found `Dimension`, `UnitChoices`, `UnitChoices.SI`,
  `Dimension.L𝓭`, and `Dimension.T𝓭`.
- Likely-name/concept query `Quantity physical dimension unit value` found
  `Dimensionful`, `WithDim`, `HasDimension`, and
  `CarriesDimension.toDimensionful`.
- Likely-name/unit query `TemperatureUnit kelvin LengthUnit meter centimeter
  nanometer TimeUnit second` found `TemperatureUnit.kelvin`,
  `LengthUnit.centimeters`, and the relevant unit-system declarations.
- Likely-name/unit query `LengthUnit.nanometers TimeUnit.seconds Dimensionful
  CarriesDimension.toDimensionful` selected `LengthUnit.nanometers`,
  `Dimensionful`, and `CarriesDimension.toDimensionful`.
- Likely-name query `DimSpeed dimensionful physical speed meters per second`
  selected Physlib's `DimSpeed`.
- Calculus query `HasDerivAt derivative constant rate motion speed` selected
  Mathlib's `HasDerivAt`. `HasConstantSpeedOnWith` was inspected as a near
  match but not used because it concerns geometric curves on sets rather than
  the problem's position and temperature readouts as functions of seconds.
- Source, module, and documentation were fetched for the final-use candidates
  `WithDim`, `Dimension`, `Dimensionful`, `CarriesDimension.toDimensionful`,
  `UnitChoices.SI`, `LengthUnit.centimeters`, `LengthUnit.nanometers`,
  `TemperatureUnit.kelvin`, `DimSpeed`, and `HasDerivAt`.

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `WithDim.val`, `Dimension.L𝓭`,
  `Dimension.T𝓭`, `Dimension.Θ𝓭`, inverse and multiplicative dimension
  notation, `DimSpeed`, `UnitChoices.SI`,
  `CarriesDimension.toDimensionful`, `LengthUnit.meters`,
  `LengthUnit.centimeters`, `LengthUnit.nanometers`, `TimeUnit.seconds`, and
  `TemperatureUnit.kelvin`.
- Mathlib: `HasDerivAt`, real absolute value, real arithmetic, and order.

## Local abstractions introduced

- Physlib provides dimensional quantities and speed but no installed API for
  rods, heaters, clamps, radioactive-source placement, or linear thermal
  expansion. The local role enums and `ThermalExpansionSetup` preserve these
  objects and geometry without reducing them to scalar placeholders.
- `HasConstantReadoutRates` connects dimensionful histories to Mathlib
  calculus through unit-explicit scalar readouts, avoiding unsupported
  derivative instances on the experimental dimensionful wrapper itself.
- `ObeysLinearThermalExpansionRateLaw` is a faithful local governing-law
  interface because LeanExplore found no dedicated thermal-expansion law.
- `RecordsProvidedFigureMismatch` preserves the contradictory primary-image
  evidence without allowing unrelated optical data to affect the thermal
  conclusion.

## Grounding gaps and redraft requests

- No Mathlib/Physlib declaration for the longitudinal linear thermal-expansion
  law was found. A local law predicate was therefore necessary.
- The requested `.archon/AGENTS.md` was absent, and the assigned Lean file did
  not yet exist. The explicit user role instructions plus
  `.archon/prover-modes/physics-formalize.md` supplied the applicable role, and
  the assigned file was created. There were no pre-existing file-specific
  `/- USER: ... -/` hints to apply.
- The `archon` executable was not available on `PATH`, so the optional DAG
  queries could not run. The source report independently confirms that there
  are no previous parts.
- The actual image at `phyx_data/test_image/156.png` depicts a laser beam and
  prism, not a heated aluminum rod. Because the chapter says to use the image
  as primary evidence, the chapter/source pairing should be redrafted or the
  image replaced. The Lean model records the mismatch explicitly and derives
  the thermal target only from the textual problem, narrated diagram, material
  calibration, and governing law.
- The theorem environment is ready for `\leanok`, but the blueprint was not
  edited because the task's write-permission section permits edits only to the
  assigned Lean file and this task-result file.

## Verification

- `archon-lean-lsp` reports no errors or warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0156.lean` succeeded.
- `lake build` succeeded.
- Source scanning found no `sorry`, `admit`, `axiom`, `sorryAx`,
  `native_decide`, or other proof escape hatch.
- `lean_verify` reports only the standard foundational dependencies
  `propext`, `Classical.choice`, and `Quot.sound` for both proved
  declarations, with no source warnings.

## Prover result (Archon iteration 014)

Complete. Both proof obligations were closed without changing their
declaration headers:

- `PhyXMiniProblems.ProblemPhyXMini0156.stated_length_and_speed_in_si`
- `PhyXMiniProblems.ProblemPhyXMini0156.problem_phyx_mini_0156`

The supporting lemma derives the exact relations
`lengthInCentimeters length = 100 * lengthInMeters length` and
`speedInNanometersPerSecond speed =
1000000000 * speedInMetersPerSecond speed` from each dimensionful quantity's
unit-coherence property. It then converts the stated `2 cm` and `100 nm/s`
readouts to `1/50 m` and `1/10000000 m/s`.

The target theorem substitutes those SI values and the aluminum coefficient
`23/1000000 K⁻¹` into the supplied expansion law
`v = alpha * d * dT/dt`. Exact rational arithmetic gives the temperature
rate `5/23 K/s`, and a final absolute-value calculation proves that it lies
within `1/2000 K/s` of answer D's `217/1000 K/s` readout.

## Blueprint marker readiness

The lemma and theorem proof environments are ready for `\leanok`. The
blueprint was not edited because this prover task explicitly restricts writes
to the assigned Lean file and this task-result file.

## Redraft needed

None for either Lean declaration. The source-image mismatch documented above
is already represented explicitly in the frozen model and does not make the
stated conclusions unprovable.
