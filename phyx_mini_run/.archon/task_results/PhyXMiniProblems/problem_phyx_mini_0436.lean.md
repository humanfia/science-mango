# Autoformalization result: `problem_phyx_mini_0436.lean`

Status: complete. The assigned Lean file compiles with only the two expected
`declaration uses sorry` warnings, one for the derived equilibrium-temperature
lemma and one for the requested piston-lift theorem.

The requested `.archon/AGENTS.md` was absent at the exact project path. I used
the supplied agent instructions and read `.archon/prover-modes/physics-formalize.md`
as the available project-local role document. The relevant target entry in
`.archon/PROGRESS.md` is objective 437.

## Assumption/target split

### Governing laws

- `ObeysTwoCompartmentThermodynamics` states:
  - final thermal equilibrium between Systems 1 and 2;
  - constant volume for rigid System 1;
  - constant pressure for piston-controlled System 2;
  - the SI ideal-gas relation `pV = nRT` for both systems at both endpoints;
  - monatomic-helium molar heat capacities `Cᵥ = 3R/2` and `Cₚ = 5R/2`;
  - `Q₁ = n₁ Cᵥ (T_f - T₁)` and `Q₂ = n₂ Cₚ (T_f - T₂)`; and
  - signed heat conservation `Q₁ + Q₂ = 0` across the internal wall.
- `ObeysFrictionlessPistonMechanics` states:
  - circular piston-face and cylinder-bore area relations;
  - equality of piston-face and bore areas for a fitting piston;
  - quasistatic force balance
    `p₂ A = p_atm A + m g` at both equilibrium endpoints; and
  - swept-volume kinematics `V₂,f - V₂,i = A h`.
- `UsesTextbookPhysicalConstants` records `R = 8.314 J mol⁻¹ K⁻¹` and
  `g = 9.81 m s⁻²` as separate textbook calibrations.
- `HasPhysicalParameters` selects positive pressures, volumes, temperatures,
  gas amounts, dimensions, areas, and heat capacities, with nonnegative lift.

### Previous-part results

- None. The source report has an empty `previous_parts` array.
- `finalEquilibriumTemperatureInKelvins` is a new derived lemma, not an assumed
  previous-part result. It concludes the common temperature is `5100/11 K`.

### Figure/data readouts

- `MatchesProblemAndPrimaryFigure` records:
  - two monatomic ideal helium samples;
  - System 1 as rigid and System 2 as frictionless-piston controlled;
  - a thin heat-conducting common wall and externally insulated combined
    apparatus;
  - `n₁ = 0.060 mol`, `T₁ = 600 K`, `n₂ = 0.030 mol`, `T₂ = 300 K`;
  - one standard atmosphere above the piston;
  - piston mass `2.0 kg` and piston diameter `10 cm`;
  - absence of direct numerical readouts for the compartment volumes and
    cylinder diameter; and
  - every visible component, label target, and connection in primary image
    `436.png`: outer container, two gas regions, separating wall, cylinder, and
    piston, with the cylinder and piston above System 2.

### Current target conclusions

- `finalEquilibriumTemperatureInKelvins` derives the useful intermediate
  `T_f = 5100/11 K` for both systems.
- `pistonLift_matches_recordedAnswerD` concludes that the independently stored
  physical lift agrees with `0.050 m` to nearest-millimetre precision and that
  none of choices A, B, or C agrees at that precision. Thus the theorem uniquely
  selects recorded answer D.

## Goal-faithfulness audit

- No assumption structure contains `0.050 m`, any answer-choice value, an
  `agreesToNearestMillimeter` proposition, or a field asserting choice D is
  physically correct.
- `HeatTransferPistonSetup.pistonLift` is an independent dimensionful field. It
  is constrained only by the ordinary swept-volume law, not defined from the
  recorded answer or from a target formula.
- Final temperatures, final volumes, heat transfers, and gas pressures are also
  independent state fields. Their relations are governing thermodynamic and
  mechanical laws.
- `recordedAnswerChoice := .D` records dataset metadata only. Unfolding it does
  not establish that the physical lift agrees with D; the substantive agreement
  and uniqueness obligations remain conclusions of the main theorem.
- The common-temperature value is proved by a separate `by sorry` lemma and is
  not inserted into any premise structure or passed as a hypothesis to the main
  theorem.
- The displayed answer is approximate under the chosen conventional constants:
  the encoded equations evaluate to about `0.0500527 m`. Therefore the target
  uses the answer's displayed millimetre precision instead of asserting a false
  exact equality to `0.050 m`.

## Declarations and blueprint labels

- `HeatTransferPistonSetup`, `MatchesProblemAndPrimaryFigure`,
  `UsesTextbookPhysicalConstants`, `HasPhysicalParameters`,
  `ObeysTwoCompartmentThermodynamics`, and
  `ObeysFrictionlessPistonMechanics` formalize the model supporting
  `thm:physics:phyx_mini_0436:target`.
- `finalEquilibriumTemperatureInKelvins` is an unlabeled derived intermediate
  supporting the same target.
- `pistonLift_matches_recordedAnswerD` is the Lean declaration corresponding to
  blueprint label `thm:physics:phyx_mini_0436:target`.

## LeanExplore queries and candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query
  `dimensionful thermodynamic quantities temperature pressure energy volume area amount of substance`
  found `Dimensionful`, `DimPressure`, and related candidates.
- Natural-language query
  `ideal gas law monatomic gas heat capacity constant volume constant pressure`
  found `IdealGas.ideal_gas_law` and
  `CanonicalEnsemble.heatCapacity`.
- Likely-name query
  `DimPressure DimArea DimEnergy Dimensionful WithDim`
  found `Dimensionful`, `DimArea`, `DimPressure`, and `DimEnergy`.
- Likely-name query `DimPressure.standardAtmosphere` found the exact standard
  atmosphere declaration.
- Source and module were fetched for the candidates used:
  - `Dimensionful` (ID 394284), module `Physlib.Units.Basic`;
  - `DimArea` (ID 394411), module `Physlib.Units.WithDim.Area`;
  - `DimPressure` (ID 394474), module `Physlib.Units.WithDim.Pressure`;
  - `DimEnergy` (ID 394468), module `Physlib.Units.WithDim.Energy`; and
  - `DimPressure.standardAtmosphere` (ID 394478), whose source fixes
    `1 atm = 101325 Pa` in `Physlib.Units.WithDim.Pressure`.
- Source and module were also inspected for the promising but incompatible
  `IdealGas.ideal_gas_law` (ID 393919). It is in
  `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` and states a
  unitless statistical-mechanics law with `R = 1`, so it cannot directly express
  this SI, mole-based two-compartment apparatus.

## Physlib/Mathlib names grounded

- `Dimensionful`, `WithDim`, `Dimension`, `L𝓭`, `T𝓭`, `M𝓭`, and `Θ𝓭` for
  dimension-carrying quantities.
- `DimArea`, `DimPressure`, and `DimEnergy` for area, pressure, and signed heat.
- `DimPressure.pascal`, `DimPressure.standardAtmosphere`, and `DimEnergy.joule`
  for named unit readouts.
- `UnitChoices.SI` for coherent-SI projections.
- `Real.pi` for circular piston and bore geometry.

An `archon-lean-lsp` standalone snippet verified all imported quantity aliases,
`DimPressure.standardAtmosphere`, `Real.pi`, and the SI projection syntax before
the file was written.

## Local abstractions introduced

- `AmountQuantity` is `Dimensionful (WithDim 1 NNReal)`. The installed Physlib
  dimension basis contains length, time, mass, charge, and temperature but no
  amount-of-substance coordinate. Retaining a dimensionful quantity plus the
  explicitly named `amountInMoles` readout is preferable to replacing gas amount
  by a transparent real scalar.
- `MolarEnergyPerTemperatureQuantity` represents `J mol⁻¹ K⁻¹`; the omitted mole
  dimension is documented and paired with a named SI readout.
- Gas samples, gas-system labels, process states, apparatus constraints, figure
  components, and label targets are local categorical types. They preserve the
  distinction between the physical objects and their scalar observations.
- The SI ideal-gas, heat-capacity, heat-transfer, force-balance, and kinematic
  relations are local governing-law structures because no compatible
  dimensionful Physlib API was found. Each relates independent physical fields
  and none states the requested numerical lift.

## Grounding gaps and redraft requests

- Physlib presently has no amount-of-substance base dimension and no directly
  compatible SI/mole ideal-gas and elementary calorimetry interface for this
  setup. The local abstractions above preserve the missing roles explicitly.
- The prose simultaneously gives a `10 cm` piston diameter and says the cylinder
  diameter is not known. The formalization distinguishes the provided piston
  diameter from the unlabelled cylinder-bore diameter, then relates their areas
  through the physical fit law. A future blueprint redraft could clarify whether
  “cylinder diameter” was intended to mean a different unprovided dimension.
- The blueprint environment was not edited to add `\leanok` because the task's
  explicit write permissions allow edits only to the assigned Lean file and this
  task-result file and specifically prohibit blueprint edits. The coordinating
  plan/blueprint agent should add `\leanok` to
  `thm:physics:phyx_mini_0436:target` after accepting this result.

## Verification

- `archon-lean-lsp` diagnostics: success, with exactly two expected `sorry`
  warnings and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0436.lean`: exit code 0,
  with the same two expected warnings.
- Independent numerical audit of the encoded laws:
  - `T_f = 463.636363636364 K`;
  - piston area `A = 0.007853981634 m²`;
  - lift `h = 0.050052668708 m`; and
  - distance from displayed `0.050 m` is `0.000052668708 m`, below the
    `0.0005 m` nearest-millimetre threshold.
