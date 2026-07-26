# Autoformalization result: `problem_phyx_mini_0151.lean`

## Assumption/target split

### Governing laws

- `SatisfiesReflectedThinFilmInterference.reflection_phase_reversal_law`: reflection from a lower to a higher refractive index contributes one half-turn (`π`), while the reverse ordering contributes none.
- `SatisfiesReflectedThinFilmInterference.round_trip_optical_path_law`: the oil round-trip optical path is `2 * n_oil * t` in every unit choice.
- `SatisfiesReflectedThinFilmInterference.constructive_reflection_law`: the propagation phase and lower-minus-upper reflection phase together equal an integral number of full turns.
- `HasPhysicalOpticalParameters`: positive refractive indices and wavelength, with nonnegative film thicknesses.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- `HasProblemReadouts` records `n_air = 1`, `n_oil = 1.50`, `n_water = 1.33`, the `580 nm` yellow wavelength, white illumination from above, upward viewing, and the normal-incidence idealization.
- `MatchesOilFilmFigure` records point A at zero horizontal distance, the pictured dark/blue/yellow/red/blue/yellow sequence, strictly increasing position and thickness along the depicted branch, and point B as the second constructive yellow fringe (order one after the first order-zero yellow fringe).
- `displayedThicknessNanometers` and `recordedDatasetAnswer` preserve the four printed options and the recorded label C as source metadata. They are not hypotheses of an optical law.

### Current target conclusions

- `reflectedInterfacePhaseDifference_eq_neg_one`: the lower-minus-upper interface phase is `-1` half-turn.
- `pointB_secondYellow_constructive_condition`: `4 * n_oil * t_B = 3 * λ_yellow` in nanometre readouts.
- `oilThicknessAtPointB_eq_290nm`: `t_B = 290 nm`, and therefore the derived thickness matches the displayed recorded choice C.

## Goal-faithfulness audit

No premise contains a numerical thickness at point B. `HasProblemReadouts` contains only source parameters; `MatchesOilFilmFigure` contains qualitative colors, ordering, and ordinal fringe identification; and the law structure is quantified over arbitrary locations, wavelengths, orders, and unit systems. The target value `290` occurs only in the answer-choice metadata and in conclusions, never in a premise field.

The recorded-choice predicate does not replace the physical goal: the theorem separately concludes the substantive equality `nanometersValue (filmThicknessAt pointB) = 290`. Unfolding answer metadata cannot establish that equality. Physically, `1 < 1.50` gives a phase reversal at air--oil, while `1.50 > 1.33` gives none at oil--water. For the second yellow fringe (`m = 1`), the general interference law yields `4 n_o t_B = (2m+1) λ = 3 λ`, hence `t_B = 3 * 580 / (4 * 1.50) = 290 nm`. This agrees with source choice C.

## Declarations and blueprint correspondence

- Blueprint target `thm:physics:phyx_mini_0151:target` is formalized by `PhyXMiniProblems.ProblemPhyXMini0151.oilThicknessAtPointB_eq_290nm`.
- Supporting proof-route declarations are `reflectedInterfacePhaseDifference_eq_neg_one` and `pointB_secondYellow_constructive_condition`.
- Unit helpers are `LengthQuantity`, `lengthValueIn`, and `nanometersValue`.
- Physical/figure vocabulary is `OpticalMedium`, `FilmInterface`, `FilmInterface.incidentMedium`, `FilmInterface.transmittedMedium`, `FilmLocation`, `ReflectedAppearance`, `IlluminationKind`, and `VerticalDirection`.
- Assumption interfaces are `OilFilmSetup`, `HasProblemReadouts`, `MatchesOilFilmFigure`, `HasPhysicalOpticalParameters`, and `SatisfiesReflectedThinFilmInterference`.
- Source-answer metadata is `AnswerChoice`, `displayedThicknessNanometers`, `MatchesDisplayedThickness`, and `recordedDatasetAnswer`.

The supporting public declarations have no separate blueprint labels. The target environment is ready for a `\lean{PhyXMiniProblems.ProblemPhyXMini0151.oilThicknessAtPointB_eq_290nm}` link and `\leanok`, but this prover did not edit the chapter because the task's write permissions explicitly forbid blueprint edits.

## LeanExplore queries/candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `thin film interference optical path refractive index phase reversal` returned only unrelated path-reversal declarations such as `Path.symm`; no optics law was usable.
- Query `Dimensionful WithDim length quantity unit choices nanometers` found and motivated use of `Dimensionful`, `LengthUnit.nanometers`, `Dimension.L𝓭`, and related unit declarations.
- Exact-name queries `Dimensionful`, `WithDim`, `LengthUnit.nanometers`, and `UnitChoices.SI` confirmed the intended APIs.
- Source, module, and docstring were fetched for `Dimensionful` (module `Physlib.Units.Basic`), `WithDim` (`Physlib.Units.WithDim.Basic`), `LengthUnit.nanometers` (`Physlib.SpaceAndTime.Space.LengthUnit`), `UnitChoices.SI` (`Physlib.Units.Basic`), and `Dimension.L𝓭` (`Physlib.Units.Dimension`).

## Grounded Mathlib/Physlib names

- `Dimensionful (WithDim Dimension.L𝓭 ℝ)` represents coherent physical lengths rather than bare scalar aliases.
- `UnitChoices`, `UnitChoices.SI`, `LengthUnit`, and `LengthUnit.nanometers` provide explicit unit selection and nanometre readouts.
- `WithDim.val` supplies the scalar projection only after a unit system has been chosen.
- `Mathlib.Data.Real.Basic` is imported directly, resolving the review gate's complaint that the target had not imported Mathlib in the real Lake environment.

## Local abstractions introduced

- The medium, interface, location, appearance, illumination, and direction inductives preserve the distinct physical and figure roles that are absent from the available library APIs.
- `OilFilmSetup` keeps dimensionful wavelengths, thicknesses, distances, and optical paths, while refractive indices and angular readouts remain dimensionless reals.
- The readout, figure, positivity, and optical-law structures separate observations from governing laws and from the requested conclusion.
- Integral half-turn phase counts preserve the physical reflection-phase role and avoid representing the requested result as a scalar definition.

## Grounding gaps and redraft requests

- LeanExplore exposed no Mathlib/Physlib thin-film-interference, refractive-index-interface, or optical-path law matching this problem, so the faithful local law interface is necessary.
- The `archon dag-query` executable advertised by the prompt was not on `PATH`; no dependency nodes could be consulted. The chapter itself lists no theorem dependencies.
- The blueprint chapter currently repeats the source and autoformalization instruction but gives no informal optical calculation. A future plan-agent redraft should state the one-phase-reversal argument, identify B as the second yellow fringe (`m = 1`), and include `4 n_o t_B = 3 λ`, yielding `290 nm`.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0151.lean`: exit 0, exactly three expected `declaration uses sorry` warnings.
- `lake lean PhyXMiniProblems/problem_phyx_mini_0151.lean`: exit 0 with the same three warnings, confirming elaboration through the declared Lake/Mathlib environment.
- A dotted per-module `lake build` target is not declared because the only library target is `PhyxMiniRun`, whose root imports only `PhyxMiniRun.Basic`; therefore the direct Lake elaboration command is the relevant target check for this standalone problem file.
