# Autoformalization result: `problem_phyx_mini_0976.lean`

## Assumption/target split

### Governing laws

- Perpendicular motional emf at every candidate speed: `E_motional = B L v` in any coherent unit system.
- Kirchhoff's loop rule together with Ohm's law: `E_battery - E_motional = I (R_bar + R_other)`.
- Magnetic force on the straight current-carrying bar: `F_B = I L B` in the signed rail direction.
- Frictionless horizontal force balance: magnetic force is the net sliding force.
- Newton's second law along the rails: `m a = F_net`.
- Terminal motion is characterized by zero rail-direction acceleration.
- The Physlib magnetic vector field is spatially and temporally uniform, points into the page, and is calibrated by the independent dimensionful flux-density magnitude.

### Previous-part results

- None. The source report has an empty `previous_parts` array, and this is a standalone problem.

### Figure/data readouts

- Written values: `L = 9/25 m`, `B = 12/5 T`, battery emf `12 V`, bar mass `9/10 kg`, bar resistance `5 Ω`, ignored external resistance `0 Ω`, and switch-closing time `0 s`.
- Written qualitative data: straight bar on parallel frictionless rails, only the bar resistance retained, uniform field into the page, and switch closure at `t = 0`.
- Primary raster `phyx_data/test_image/976.png`: two horizontal parallel rails, a vertical bar bridging them, crosses throughout the rail region, labels `B`, `ε`, `S`, and `L`, an open switch, the positive battery terminal toward the upper rail, and a vertical `L` marker spanning the rails. The image has no motion arrow or terminal-speed readout.
- Direction conventions entering the physical laws: the battery drives current downward through the bar; with the pictured into-page field, the drive force and chosen positive sliding direction are rightward.
- The auxiliary generated caption says the bar is horizontal and moves vertically. This contradicts the primary raster, so the Lean model correctly follows the primary image instead.

### Current target conclusions

- The exact coherent-SI terminal-speed readout is `125/9 m/s`.
- Its distance from displayed choice B (`14 m/s`) is exactly `1/9 m/s`.
- B is strictly closer than A (`12 m/s`), C (`2.4 m/s`), or D (`8.64 m/s`).

## Goal-faithfulness audit

- `SlidingBarRailSetup.terminalSpeed` is an independent `DimSpeed`; it is not defined as `E/(B L)` or as a numeric answer.
- `motionalEmfAt`, `circuitCurrentAt`, `magneticForceAt`, `netSlidingForceAt`, and `accelerationAt` are independent physical observables. Their relationships occur only in the governing-law structure.
- `IsTerminalSpeed` asserts only that the signed rail acceleration has SI readout zero. It contains no numeric speed, answer choice, emf balance, or target formula.
- No scenario, figure, measurement, positivity, field-model, or governing-law field contains `125/9`, choice B, or the derived formula `E/(B L)`.
- The formula `v = E/(B L)` appears only as the conclusion of `terminalSpeed_eq_batteryEmf_div_field_length`. The numerical value and closest-choice result appear only in the conclusion of `problem_phyx_mini_0976`.
- `recordedDatasetAnswer := .B` preserves source metadata only. It is not a theorem premise and does not define the physical speed or the closest-choice predicate.
- Mass and resistance remain explicit apparatus/dynamics parameters even though they control the transient rather than the ideal limiting speed.

## Source/law/answer audit

- From terminal zero acceleration and positive mass, Newton's law gives zero net force. Frictionless force balance gives zero magnetic force; positive `L` and `B` then give zero current from `F_B = I L B`.
- The Kirchhoff--Ohm law therefore reduces to equality of battery and motional emfs, and the motional-emf law yields `v = E/(B L)`.
- With the supplied numbers, `12 / ((12/5) * (9/25)) = 125/9 ≈ 13.888... m/s`. Thus the recorded answer B (`14 m/s`) is physically supported as the nearest displayed choice, while `14 m/s` is not asserted as the exact terminal speed.

## Declarations and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0976:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0976.problem_phyx_mini_0976`.
- The supporting derived declaration is `PhyXMiniProblems.ProblemPhyXMini0976.terminalSpeed_eq_batteryEmf_div_field_length`.
- Supporting model declarations include the physical dimension constants and quantity/readout types; `SlidingBarRailFigure`; `SlidingBarRailSetup`; scenario, figure, measurement, physical-parameter, field, and governing-law structures; `IsTerminalSpeed`; `AnswerChoice`; and `IsUniqueClosestAnswer`.
- Both proof-bearing declarations have `by sorry` bodies, as required in the autoformalize stage.

## LeanExplore queries/candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`. Queries issued in this post-formalization audit were:

- `motional emf moving conducting rod magnetic field length speed B L v`
- `Ohm's law voltage current resistance magnetic force current carrying wire`
- `Dimensionful WithDim DimSpeed UnitChoices.SI`
- `Electromagnetism.MagneticField`
- `WithDim`
- `DimSpeed`
- `Dimension`

The first query returned electromagnetic-potential and field-strength declarations, not a lumped sliding-rod motional-emf law. The second returned infinite-wire/current-density and Gauss--Ampère declarations, not compatible Ohm or straight-bar force laws.

Candidates whose module and source were fetched and then used:

- `Dimension` (id 394292), `Physlib.Units.Dimension`.
- `Dimensionful` (id 394284), `Physlib.Units.Basic`.
- `WithDim` (id 394425), `Physlib.Units.WithDim.Basic`.
- `DimSpeed` (id 394481), `Physlib.Units.WithDim.Speed`.
- `UnitChoices.SI` (id 394270), `Physlib.Units.Basic`.
- `Electromagnetism.MagneticField` (id 385560), `Physlib.Electromagnetism.Basic`.

## Physlib/Mathlib names grounded

- Physlib `Dimension` and base dimensions `L𝓭`, `T𝓭`, `M𝓭`, and `C𝓭` encode length, time, mass, and charge exponents.
- `Dimensionful (WithDim d M)` represents a unit-independent scalar physical quantity with dimension `d`; `DimSpeed` is the existing nonnegative speed type.
- `UnitChoices.SI` supplies the metres/seconds/kilograms/coulombs/kelvin coherent-unit readout boundary.
- `Electromagnetism.MagneticField 3` supplies the spacetime-dependent three-dimensional vector-field role.
- Mathlib `NNReal`, `EuclideanSpace ℝ (Fin 3)`, real absolute value/arithmetic, and finite inductive types support nonnegative magnitudes, directions, and answer comparison.

## Local abstractions introduced

- Derived electromagnetic dimensions are composed from Physlib base dimensions because no ready-made voltage, current, resistance, force, acceleration, or tesla scalar quantity with the required school-level interface was found.
- `SlidingBarRailFigure` and finite vocabularies preserve literal component, label, geometry, switch, polarity, and field-glyph evidence without turning the image into an answer premise.
- `SlidingBarRailSetup` keeps the speed, emf, current, force, and acceleration roles distinct and dimensionful rather than collapsing them to transparent real aliases.
- `ModelsUniformIntoPageMagneticField` bridges Physlib's nondimension-tagged vector field to a separate dimensionful tesla magnitude and explicit constant-field calibration.
- `SatisfiesBatteryDrivenSlidingBarLaws` states the missing motional-emf, Kirchhoff--Ohm, straight-wire-force, frictionless-balance, and Newton-law interface explicitly.
- `IsTerminalSpeed` formalizes the dynamic zero-acceleration condition; `IsUniqueClosestAnswer` separately formalizes multiple-choice comparison.

## Grounding gaps and redraft requests

- LeanExplore exposed no compatible ready-made theorem for the battery-driven sliding rod, `E = B L v`, the lumped Kirchhoff--Ohm equation, or `F = I L B`; the explicit local law interface is therefore necessary.
- `Electromagnetism.MagneticField` is a spacetime vector field whose codomain is not dimension-tagged, requiring the explicit dimensionful magnitude/calibration bridge.
- The blueprint contains `% archon:physics` but only the generic autoformalization directive, not the informal derivation. A plan-agent redraft should add the zero-acceleration-to-zero-current derivation and numerical calculation above.
- The primary raster and auxiliary caption disagree about bar orientation/motion; the caption should be corrected to describe a vertical bar sliding horizontally.
- The requested `.archon/AGENTS.md` is absent. The complete `.archon/prover-modes/physics-formalize.md`, `.archon/PROGRESS.md`, and supplied task instructions were used instead.
- The advertised `archon` command is not available on `PATH`, so DAG queries could not run. The source report independently confirms there are no previous parts.
- The blueprint was not edited with `\\leanok` because the explicit write permissions prohibit blueprint edits. A blueprint-authorized coordinator should mark the target environment after accepting this file.

## Retry resolution and verification

- Gate reason: review iteration 001 failed only because no post-formalization task result existed at review time. This file is the required current evidence and records actual-used searches, candidates, names, abstractions, gaps, and the source/law/answer split.
- `archon-lean-lsp` diagnostics succeeded with only two expected `declaration uses sorry` warnings, at the derived lemma and final theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0976.lean` exited 0 with only those same two expected warnings.
