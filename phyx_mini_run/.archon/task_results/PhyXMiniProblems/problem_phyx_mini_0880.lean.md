# Autoformalization result: `problem_phyx_mini_0880.lean`

## Assumption/target split

### Governing laws

- `SatisfiesIdealMixedCapacitorCircuitLaws.capacitorChargeLaw` states the
  ideal-capacitor constitutive relation `Q = C V` for each of `C₁`, `C₂`, and
  `C₃`, using coherent-SI scalar readouts of dimensionful quantities.
- `equalPotentialDifferenceOnParallelPair` states the common voltage across
  `C₁` and `C₂`.
- `sourcePotentialDifferenceBalance` states the Kirchhoff voltage balance
  between the parallel branch, `C₃`, and the battery.
- `floatingJunctionChargeConservation` states charge conservation at the
  floating node: the charge magnitude on `C₃` equals the sum of those on the
  two parallel capacitors.
- `HasPhysicalMixedCapacitorParameters` records positive capacitances and
  source voltage, together with nonnegative voltage and charge magnitudes.

### Previous-part results

- None. The source report contains no previous parts.

### Figure/data readouts

- `MatchesSuppliedMixedCapacitorFigure` records the `9 V` battery label; the
  `C₁ = 4 μF`, `C₂ = 12 μF`, and `C₃ = 2 μF` labels; all three capacitor
  symbols; the positive and negative battery terminals; and the three-node
  connectivity visible in `880.png`.
- The plate-node equalities put `C₁` and `C₂` between the positive rail and
  the common junction and put `C₃` between that junction and the negative
  rail. Thus the parallel/series topology is preserved explicitly rather
  than hidden in a precomputed equivalent capacitance.
- `AnswerChoice.chargeInMicrocoulombs` records the displayed values
  `2.5`, `15`, `55`, and `16 μC`; `recordedDatasetAnswer` records metadata
  label `D`.

### Current target conclusions

- `charge_on_c3_eq_sixteen_microcoulombs`: the charge magnitude on `C₃` is
  `16 μC`.
- `charge_on_c3_matches_recorded_choice`: the same physical charge equals
  `16 μC`, the metadata label is `D`, and the charge equals the value printed
  for that choice.

## Goal-faithfulness audit

The target value `16 μC` and recorded choice `D` do not occur in
`MixedCapacitorCircuitSetup`, `MatchesSuppliedMixedCapacitorFigure`,
`HasPhysicalMixedCapacitorParameters`, or
`SatisfiesIdealMixedCapacitorCircuitLaws`. The only `16` outside the target
section is the conclusion of the derived lemma
`parallel_branch_capacitance_readout`, where it is the sum of the independent
`4 μF` and `12 μF` figure labels, not a charge assumption. The junction
equation is a general charge-conservation law and does not supply a numerical
charge. The unknown capacitor charge is an independent field of the setup and
is not defined by unfolding an answer choice.

The premises are also sufficient for the intended calculation: if the common
parallel-branch voltage is `V_p` and the `C₃` voltage is `V₃`, the premises
give `9 = V_p + V₃` and `2 V₃ = (4 + 12) V_p` in the common micro-scaled
units, hence `V_p = 1 V`, `V₃ = 8 V`, and `Q₃ = 2 μF · 8 V = 16 μC`.

## Declarations and blueprint mapping

- Dimension/readout declarations:
  `potentialDifferenceDimension`, `capacitanceDimension`,
  `CapacitanceQuantity`, `ChargeMagnitudeQuantity`,
  `PotentialDifferenceQuantity`, `capacitanceInFarads`,
  `capacitanceInMicrofarads`, `chargeInCoulombs`,
  `chargeInMicrocoulombs`, and `potentialDifferenceInVolts`.
- Figure/setup declarations:
  `CapacitorId`, `CircuitNode`, `BatteryTerminal`,
  `MixedCapacitorCircuitFigure`, `MixedCapacitorCircuitSetup`, and their
  expected-label helpers.
- Premise declarations:
  `MatchesSuppliedMixedCapacitorFigure`,
  `HasPhysicalMixedCapacitorParameters`, and
  `SatisfiesIdealMixedCapacitorCircuitLaws`.
- Answer/derived declarations:
  `AnswerChoice`, `AnswerChoice.chargeInMicrocoulombs`,
  `recordedDatasetAnswer`, `parallel_branch_capacitance_readout`, and
  `charge_on_c3_eq_sixteen_microcoulombs`.
- Blueprint label `thm:physics:phyx_mini_0880:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0880.charge_on_c3_matches_recorded_choice`.

## LeanExplore grounding

Queries were run with `packages: ["Mathlib", "Physlib"]`:

- `electric capacitor capacitance charge voltage physical dimensions SI units`
- `capacitors connected in parallel and series equivalent capacitance`
- `Capacitance Charge Voltage capacitor`
- `unit microfarad microcoulomb volt SI`
- `ElectricPotentialUnit volt electromagnetic voltage unit`
- `capacitance physical dimension farad`
- `Dimensional quantity with physical dimension and unit system`
- `MeasureReal dimensional quantity SI`
- `WithDim`

Candidates inspected and used were:

- `Dimension` from `Physlib.Units.Dimension`;
- `Dimension.C𝓭` from `Physlib.Units.Dimension`;
- `WithDim` from `Physlib.Units.WithDim.Basic`;
- `Dimensionful` and `UnitChoices.SI` from `Physlib.Units.Basic`.

The sources of `WithDim.withDim_hMul_val`, `WithDim.val_div_val`,
`WithDim.val_add`, and `WithDim.cast` were inspected to confirm the available
dimension-tagged arithmetic, although the formalization deliberately states
the school-level circuit laws through coherent-SI readouts. `ChargeUnit` and
`ChargeUnit.coulombs` were also inspected; they describe unit choices rather
than physical charge quantities, so they were not used as a substitute for
`Dimensionful (WithDim Dimension.C𝓭 NNReal)`.

Mathlib's `NNReal` is used for nonnegative capacitance, charge magnitude, and
potential-difference magnitude readouts. A standalone LSP snippet verified
the dimension expressions, `Dimensionful` specializations, and SI readout
syntax before the file was written.

## Local abstractions introduced

- Physlib does not expose a named farad/capacitance quantity in the search
  results, so `capacitanceDimension = C² T² M⁻¹ L⁻²` was defined and used with
  Physlib's unit-independent `Dimensionful`/`WithDim` framework.
- `potentialDifferenceDimension = M L² T⁻² C⁻¹` was defined for the voltage
  magnitudes.
- The component IDs, conductor nodes, battery terminals, raw figure record,
  setup record, and circuit-law predicate are local because no matching
  capacitor-network API was found. They preserve component identity,
  topology, dimensions, observables, and governing laws without reducing a
  physical primitive to a scalar alias.

## Grounding gaps and redraft requests

- LeanExplore returned no applicable Mathlib/Physlib declaration for ideal
  capacitors, equivalent capacitance, series/parallel capacitor networks,
  farads, or Kirchhoff laws. The local abstractions above fill that gap.
- The requested `.archon/AGENTS.md` was absent from the project; the complete
  `.archon/prover-modes/physics-formalize.md` role file was read instead.
- The `archon` executable was not present on `PATH`, so the optional DAG query
  could not be run. The chapter itself contains no dependency labels beyond
  the target.
- The blueprint target should receive `\lean{PhyXMiniProblems.ProblemPhyXMini0880.charge_on_c3_matches_recorded_choice}`
  and `\leanok`. It was not edited because this task's explicit write
  permissions allow changes only to the assigned Lean file and this result
  file.
