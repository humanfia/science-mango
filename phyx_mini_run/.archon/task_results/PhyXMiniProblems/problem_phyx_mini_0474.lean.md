# Autoformalization result: `problem_phyx_mini_0474.lean`

## Outcome

- Finalized `PhyXMiniProblems/problem_phyx_mini_0474.lean` as a dimension-aware Carnot-engine formalization.
- Addressed the iteration-001 review-gate reason, “physics target does not import Mathlib,” by adding an explicit root `import Mathlib` while retaining the Physlib temperature and energy imports.
- Confirmed the chapter contains `% archon:physics`; the `physics-formalize` discipline was used.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0474.lean` exits successfully. Its only diagnostics are the three required `declaration uses sorry` warnings.
- `.archon/AGENTS.md` is absent from this workspace. The user-supplied role, `.archon/PROGRESS.md`, and `.archon/prover-modes/physics-formalize.md` were used as the available role guidance.

## Physical model extracted

- The device is a reversible Carnot heat engine operating between a hot reservoir and a cold reservoir.
- Absolute reservoir temperatures are physical `Temperature` values with an explicit `TemperatureUnit` storage unit. The primary image gives `T_H = 500 K` and `T_C = 350 K`.
- Absorbed heat, rejected heat, and net work are physical `DimEnergy` values. Their explicitly named scalar projections are joule readouts. The primary image gives `Q_H = 2000 J` and marks `Q_C` and `W` unknown.
- Efficiency is dimensionless. The image marks it unknown.
- Diagram nodes, three directed arrows, orientations, displayed labels, and unknown markers preserve the geometry and labels visible in `phyx_data/test_image/474.png`.
- The displayed answer choices are 36%, 30%, 28%, and 45%; dataset metadata records choice B, 30%.

## Assumption/target split

### Governing laws

- `SatisfiesCarnotHeatEngineLaws.cycleEnergyBalance`: for positive transfer magnitudes, `W = Q_H - Q_C` over one cycle.
- `SatisfiesCarnotHeatEngineLaws.thermalEfficiencyDefinition`: `e = W / Q_H`.
- `SatisfiesCarnotHeatEngineLaws.reversibleHeatTemperatureRatio`: reversibility gives `Q_C / Q_H = T_C / T_H`.
- `HasPhysicalCarnotEngineParameters` supplies positivity, the reservoir ordering `T_C < T_H`, nonnegativity of rejected heat and work, and the physical range `0 ≤ e < 1`.

### Previous-part results

- None. The source report has `previous_parts: []`.

### Figure/data readouts

- The prose identifies the role as a heat engine and the model as Carnot.
- Temperatures are stored in kelvins, with scalar readouts `T_H = 500` and `T_C = 350`.
- The absorbed-heat readout is `Q_H = 2000 J`.
- All six textual labels are shown. `T_H`, `Q_H`, and `T_C` are supplied; `W`, `e`, and `Q_C` are explicitly marked unknown.
- The heat-input and rejected-heat arrows point downward through the engine, while the work arrow points rightward from the engine to the exterior.

### Current target conclusions

- `rejectedHeat_inJoules_eq_1400`: derive `Q_C = 1400 J` from the reversible heat/temperature ratio and figure data.
- `netWorkOutput_inJoules_eq_600`: derive `W = 600 J` from the first law and figure data.
- `carnotEfficiency_eq_recordedAnswerB`: derive `e = 3/10`, hence `100e = 30`, and identify the displayed value with recorded answer choice B.

## Goal-faithfulness audit

The current numeric conclusions are not fields of `CarnotHeatEngineSetup`, `MatchesProblemStatement`, `MatchesPrimaryHeatEngineFigure`, `HasPhysicalCarnotEngineParameters`, or `SatisfiesCarnotHeatEngineLaws`. In particular, the figure predicate records that rejected heat, work, and efficiency are unknown rather than supplying their answers. The laws state only general cycle relations and do not contain `1400`, `600`, `3/10`, or `30`. `recordedAnswerChoice` and the answer-choice percentage table are source metadata; they do not determine `setup.thermalEfficiency`. The final theorem must connect the independently modeled efficiency to that metadata.

The physical quantities are not collapsed to real aliases: temperature uses Physlib's `Temperature`, and heat/work use Physlib's dimensionful `DimEnergy`. Reals occur only for unit-labelled scalar readouts, dimensionless efficiency, and displayed percentages.

## Declarations and blueprint correspondence

The substantive target corresponds to blueprint label `thm:physics:phyx_mini_0474:target`:

- `carnotEfficiency_eq_recordedAnswerB` — main formalization target.

Public supporting declarations under the same target environment (the chapter has no separate labels for these helpers):

- Unit-aware vocabulary: `TemperatureQuantity`, `EnergyQuantity`, `energyInJoules`, `temperatureInKelvins`.
- Scenario/figure vocabulary: `ThermodynamicDeviceRole`, `HeatEngineModel`, `Reservoir`, `DiagramNode`, `DiagramArrow`, `ArrowOrientation`, `FigureLabel`, `HeatEngineDiagram`, `CarnotHeatEngineSetup`.
- Assumption interfaces: `MatchesProblemStatement`, `MatchesPrimaryHeatEngineFigure`, `HasPhysicalCarnotEngineParameters`, `SatisfiesCarnotHeatEngineLaws`.
- Derived-result lemmas: `rejectedHeat_inJoules_eq_1400`, `netWorkOutput_inJoules_eq_600`.
- Source-answer metadata: `AnswerChoice`, `AnswerChoice.efficiencyPercent`, `recordedAnswerChoice`.

These helpers are needed to preserve the physical roles, primary-image geometry/readouts, governing laws, and source answer metadata. A later blueprint-maintenance pass may add individual environments if the project requires every public helper to have its own label.

## LeanExplore queries/candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Natural-language query `thermodynamic absolute temperature Kelvin temperature unit` found and motivated use of `Temperature` (id 394201), `TemperatureUnit` (id 394233), and `TemperatureUnit.kelvin` (id 394250).
- Likely-name query `Temperature TemperatureUnit kelvin` confirmed `TemperatureUnit.kelvin`, `TemperatureUnit`, and `UnitChoices.SI`.
- Likely-name query `Temperature.toReal` found `Temperature.toReal` (id 394203), used by `temperatureInKelvins`.
- Natural-language query `dimensionful physical energy joule SI units` found `DimEnergy.joule` (id 394469), `Dimensionful`, and `UnitChoices.SI` (id 394270).
- Likely-name query `DimEnergy joule` confirmed `DimEnergy` (id 394468) and `DimEnergy.joule`.
- Natural-language query `Carnot heat engine efficiency one minus cold temperature divided by hot temperature` found temperature infrastructure but no Carnot-engine efficiency or reversible-cycle declaration.

Source and module data were fetched for every candidate directly used: `Temperature` and `Temperature.toReal` from `Physlib.Thermodynamics.Temperature.Basic`; `TemperatureUnit` and `TemperatureUnit.kelvin` from `Physlib.Thermodynamics.Temperature.TemperatureUnits`; `DimEnergy` and `DimEnergy.joule` from `Physlib.Units.WithDim.Energy`; and `UnitChoices.SI` from `Physlib.Units.Basic`.

## Physlib/Mathlib names grounded

- Physlib: `Temperature`, `Temperature.toReal`, `TemperatureUnit`, `TemperatureUnit.kelvin`, `DimEnergy`, `DimEnergy.joule`, and `UnitChoices.SI`.
- LeanExplore source confirms that `Temperature` wraps a nonnegative absolute-temperature value and that `DimEnergy` has energy dimension `M L² T⁻²`.
- Mathlib: root `Mathlib` is imported explicitly as required by the review gate. Standard `ℝ`, `NNReal`, finite/decidable derivations, and arithmetic notation elaborate in the project environment. No specialized Mathlib theorem is needed at this by-`sorry` stage.

## Local abstractions introduced

- `energyInJoules` is a named scalar readout of a `DimEnergy`, evaluated in `UnitChoices.SI` relative to `DimEnergy.joule`; it is not a replacement physical quantity.
- `temperatureInKelvins` is a named scalar readout converting the stored absolute-temperature value using the ratio of its `TemperatureUnit` to `TemperatureUnit.kelvin`.
- The diagram enums and `HeatEngineDiagram` are the smallest local representation retaining the bitmap's labels, nodes, arrow directions, and unknown markings.
- The setup and four proposition-valued interfaces separate physical state, prose classification, primary-image evidence, operating conditions, and governing laws.
- `SatisfiesCarnotHeatEngineLaws` is local because LeanExplore found no ready-made Physlib/Mathlib Carnot heat-engine API. It states general physical relations rather than the requested numeric answer.

## Grounding gaps

- No ready-made Carnot-engine object, Carnot efficiency law, cycle energy balance, or reversible heat/temperature-ratio declaration was found in Mathlib/Physlib. The faithful local law interface records this missing infrastructure.
- No dedicated library function for a `DimEnergy` joule scalar readout was found; `energyInJoules` uses the grounded dimensionful SI representation and `DimEnergy.joule`.
- The optional `archon dag-query` navigation command was unavailable on `PATH` in this runtime, so no dependency-graph result was used.

## Source/law/answer audit

The primary image, chapter, and source JSON agree on `500 K`, `350 K`, `2000 J`, and unknown `Q_C`, `W`, and `e`. Under the explicitly modeled reversible Carnot laws, `Q_C/Q_H = 350/500`, so `Q_C = 1400 J`; the first law gives `W = 600 J`; and `e = W/Q_H = 0.30`. Thus answer B is physically supported and agrees with the recorded answer.

## Redraft requests and handoff

- No semantic source redraft is requested.
- The chapter was not edited to add `\leanok`, because this task's explicit write permissions forbid editing blueprint chapters. The blueprint owner/coordinator should mark the target environment `\leanok` after accepting this compiling formalization.
