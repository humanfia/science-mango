# Autoformalization result: `problem_phyx_mini_0363.lean`

## Assumption/target split

### Governing laws

- The fixed gas obeys the ideal-gas relation `p * V = n * R * T` at both
  labelled endpoints. The relation is expressed in atmosphere,
  cubic-centimetre, mole, and kelvin readouts.
- The plotted inverse pressure-volume curve has constant `p * V` from point
  `1` to point `2`.
- Both endpoint states have positive pressure, volume, and absolute-temperature
  readouts.
- The standard molar gas constant used for the numerical evaluation is
  `82.057 atm·cm³/(mol·K)`.

### Previous-part results

- None; the source report has an empty `previous_parts` list.

### Figure/data readouts

- The gas amount stated in the problem is `0.020 mol`.
- The primary bitmap has volume in `cm³` on the horizontal axis and pressure in
  `atm` on the vertical axis.
- Point `1` is `(V₁, p₁) = (400 cm³, 3 atm)`.
- Point `2` has `p₂ = 1 atm`; its coordinate is labelled `V₂` and is not
  assumed numerically.
- The arrow is directed from point `1` to point `2`; pressure decreases and
  volume increases along the inverse curve.
- The supplied choices are `458 °C`, `756 °C`, `356 °C`, and `584 °C`, with
  recorded answer A.

### Current target conclusions

- The final point-2 kelvin temperature, converted with the affine `273.15`
  Celsius offset, lies within half a degree of `458 °C`; equivalently it rounds
  to displayed answer A.

## Goal-faithfulness audit

No hypothesis fixes the final volume or final temperature, and no premise
contains `458`. `FollowsInversePVcurve` states only the figure-derived
constant-`pV` relation. `SatisfiesIdealGasLaw` is a generic governing law over
an arbitrary state, amount, and gas constant. The amount, gas-constant, and
point-coordinate hypotheses are source/physical data rather than the requested
answer.

`kelvinToCelsius` and `RoundsToNearestDegreeCelsius` are generic conversion and
rounding predicates: neither definition mentions this problem's answer. The
number `458` appears only in the theorem conclusion. The rounded relation is
used because the calibrated gas constant gives approximately `458.05 °C`, not
an exact equality to the displayed whole-degree choice.

## Declarations created and blueprint correspondence

- Quantity/readout layer: `VolumeQuantity`, `PressureQuantity`,
  `TemperatureQuantity`, `pressureInPascals`, `pressureInAtmospheres`,
  `volumeInCubicCentimeters`, and `temperatureInKelvins`.
- Physical setup: `GasState` and `DirectedGasProcess`.
- Assumption layer: `HasPositiveReadouts`, `SatisfiesIdealGasLaw`, and
  `FollowsInversePVcurve`.
- Generic answer semantics: `kelvinToCelsius` and
  `RoundsToNearestDegreeCelsius`.
- Target theorem: `PhyXMiniProblems.ProblemPhyXMini0363.finalTemperatureRoundsTo458C`,
  corresponding to blueprint label `thm:physics:phyx_mini_0363:target`.

The supporting declarations serve this single blueprint target and have no
independent blueprint labels. The chapter was not edited because the role's
explicit write permissions allow only the assigned Lean file and this result
file; a blueprint-owning agent should add `\leanok` after review.

## LeanExplore queries and candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- `ideal gas law pressure volume amount of substance temperature gas constant`
  and `IdealGas idealGasLaw` found `IdealGas.ideal_gas_law`, `Temperature`,
  `Temperature.toReal`, and `DimPressure`.
- `physical dimensions pressure volume temperature amount of substance` and
  `SI quantity pressure volume thermodynamic temperature mole` found
  `Dimension`, `Dimensionful`, `DimPressure`, and `UnitChoices.SI`.
- `DimVolume cubic meter` and `Dimensional volume physical quantity` checked
  for a ready-made volume type and found only the general `Dimensionful` /
  `WithDim` infrastructure.
- `temperature Celsius Kelvin conversion` found `Temperature`,
  `Temperature.toReal`, `TemperatureUnit`, and `TemperatureUnit.kelvin`.
- `atmosphere pressure unit atm` found `DimPressure.standardAtmosphere`.
- `mole amount of substance physical quantity` checked for an
  amount-of-substance quantity API.
- `TemperatureUnit.kelvin UnitChoices.SI WithDim Dimensionful` grounded the
  exact unit declarations used in the file.

Source and module data were fetched for `IdealGas.ideal_gas_law`,
`DimPressure`, `DimPressure.standardAtmosphere`, `Temperature`,
`Temperature.toReal`, `TemperatureUnit`, `TemperatureUnit.kelvin`,
`UnitChoices.SI`, `Dimension`, and `Dimensionful` before use or rejection.

## Physlib/Mathlib names grounded

- `DimPressure` and `DimPressure.standardAtmosphere` from
  `Physlib.Units.WithDim.Pressure` provide physical pressure and the standard
  atmosphere calibration.
- `Temperature`, `Temperature.toReal`, `TemperatureUnit`, and
  `TemperatureUnit.kelvin` provide absolute temperature and kelvin scaling.
- `Dimensionful`, `WithDim`, `Dimension.L𝓭`, and `UnitChoices.SI` provide a
  dimension-tagged `L³` volume and coherent-SI readout.
- `NNReal` enforces nonnegativity of the underlying volume and supports the
  positive temperature-unit ratio.

## Local abstractions introduced

- `VolumeQuantity` assembles the smallest Physlib-backed volume type from
  `Dimensionful (WithDim L³ NNReal)`. It is dimension-tagged and nonnegative,
  not a scalar alias.
- `GasState` preserves distinct pressure, volume, and absolute-temperature
  roles. `DirectedGasProcess` retains the two figure labels and arrow order.
- `SatisfiesIdealGasLaw` states the actual `pV = nRT` law in the units printed
  by the problem. It does not encode the final answer.
- `FollowsInversePVcurve` records the governing relation represented by the
  plotted hyperbola without assuming a final volume or temperature.
- The local Celsius and nearest-degree definitions make the affine unit
  conversion and multiple-choice rounding explicit.

## Grounding gaps and redraft requests

- `IdealGas.ideal_gas_law` is a near match, but its source is a specialized
  unitless microcanonical model with internally computed pressure and `R = 1`.
  It is incompatible with molar data in `atm·cm³/(mol·K)`, so the faithful
  chart-unit law predicate is local.
- No ready-made `DimVolume` or cubic-centimetre unit was found. Volume is built
  from Physlib's dimensional infrastructure, and its scalar readout performs
  the standard `m³` to `cm³` conversion.
- Physlib's foundational `Dimension` has length, time, mass, charge, and
  temperature coordinates but no amount-of-substance coordinate. The stated
  `0.020 mol` is therefore kept as an explicitly unit-labelled scalar readout,
  which is permitted for measured numerical components.
- No affine Celsius API was found in the zero-preserving temperature-unit
  layer, so the `273.15` offset is explicit locally.
- The blueprint environment supplies no informal derivation beyond the
  autoformalization directive. A future plan redraft could explicitly state
  the route `p₁V₁ = p₂V₂`, then `p₂V₂ = nRT₂`, followed by Celsius conversion
  and rounding.
- The requested `.archon/AGENTS.md` is absent in this checkout; the available
  `.archon/prover-modes/physics-formalize.md` and `PROGRESS.md` were followed.
  The advertised `archon` executable was also not on `PATH`, so the dependency
  graph query could not run.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0363.lean` exits successfully
with only the expected `declaration uses 'sorry'` warning for the target
theorem.
