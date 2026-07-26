# Physics autoformalization result: `problem_phyx_mini_0619.lean`

## Assumption/target split

### Governing laws

- `ValidDosePhysics.interaction_transmission_partition`: interacting and transmitted gamma fractions sum to one.
- `ValidDosePhysics.gamma_radiation_weighting_factor`: gamma radiation has weighting factor one.
- `ValidDosePhysics.decays_during_exposure`: the decay count is activity in becquerels times exposure time in seconds.
- `ValidDosePhysics.isotropic_point_source_interception`: the worker intercepts the fraction `area / (4 * Real.pi * distance^2)` of an isotropic point-source flux.
- `ValidDosePhysics.deposited_energy`: both cobalt-60 gamma-line energies contribute on each decay, and the interacting fraction deposits all intercepted energy.
- `ValidDosePhysics.absorbed_whole_body_dose`: absorbed dose is deposited energy divided by worker mass.
- `ValidDosePhysics.gamma_equivalent_dose`: equivalent gamma dose is absorbed dose times the radiation weighting factor.

These are generic relations between the setup and independently represented intermediate results. None states a numerical dose or answer choice.

### Previous-part results

- None. The source report's `previous_parts` list is empty.

### Figure/data readouts

- Nuclide: cobalt-60.
- Source activity: `40 mCi`.
- Worker mass: `70 kg`.
- Body cross-sectional area: `1.5 m^2`.
- Figure-derived radial source-to-worker distance: `4.0 m`.
- Daily exposure: `4.0 h`.
- Gamma energies emitted in quick succession: `1.33 MeV` and `1.17 MeV`.
- Interacting/deposited fraction: `1/2`; transmitted fraction: `1/2`.

These readouts are fields of `MatchesProblemData`; that structure contains no dose value, closeness bound, or selected answer.

### Current target conclusions

- The computed equivalent whole-body dose is within `0.005 mSv` of `0.45 mSv`, the recorded precision of choice C.
- Choice C is strictly closer to the computed dose than every distinct listed answer choice.

## Goal-faithfulness audit

The target dose and answer-selection claims occur only in the conclusion of `dailyWholeBodyDose_is_choice_C`. Neither `MatchesProblemData` nor `ValidDosePhysics` assumes `0.45 mSv`, choice C, a rounding/closeness result, or the target dose. `doseInMilliSieverts` merely converts the independently calculated equivalent specific-energy SI readout to millisieverts; unfolding it cannot produce an answer choice.

The theorem therefore still requires the activity-time decay law, spherical interception, two-photon energy sum, deposition fraction, energy-per-mass law, gamma weighting, and unit conversions. Directly evaluating the stated central values gives approximately `0.4548917 mSv`, which is within `0.005 mSv` of C and is strictly farther from A, B, and D.

The source's “about” and “approximately” inputs are represented by their displayed central values in `MatchesProblemData`; the target is correspondingly a displayed-precision bound rather than a false exact equality to `0.45`.

## Declarations and blueprint labels

- `PhyXMini0619.dailyWholeBodyDose_is_choice_C` — `thm:physics:phyx_mini_0619:target`.
- `DimLength`, `DimTime`, `DimMass`, `DimActivity`, `DimSpecificEnergy` — respectively `def:physics:phyx-mini-0619:phyxmini0619-dimlength`, `...-dimtime`, `...-dimmass`, `...-dimactivity`, and `...-dimspecificenergy`.
- `lengthInMeters`, `timeInSeconds`, `timeInHours`, `massInKilograms` — respectively `...-lengthinmeters`, `...-timeinseconds`, `...-timeinhours`, and `...-massinkilograms` under the same `def:physics:phyx-mini-0619:phyxmini0619` prefix.
- `activityInBecquerels`, `activityInMilliCuries`, `areaInSquareMeters` — respectively `...-activityinbecquerels`, `...-activityinmillicuries`, and `...-areainsquaremeters`.
- `energyInJoules`, `energyInMegaElectronVolts`, `specificEnergyInSI` — respectively `...-energyinjoules`, `...-energyinmegaelectronvolts`, and `...-specificenergyinsi`.
- `Nuclide`, `Cobalt60Exposure`, `WholeBodyDose`, `DoseComputation` — respectively `...-nuclide`, `...-cobalt60exposure`, `...-wholebodydose`, and `...-dosecomputation`.
- `MatchesProblemData`, `ValidDosePhysics` — respectively `...-matchesproblemdata` and `...-validdosephysics`.
- `doseInMilliSieverts`, `DoseAnswerChoice`, `answerValueMilliSievert` — respectively `...-doseinmillisieverts`, `...-doseanswerchoice`, and `...-answervaluemillisievert`.

No extra public declarations were added beyond the topology recorded in the blueprint chapter.

## LeanExplore queries and candidates actually used

Every search used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `radioactive activity absorbed dose equivalent dose sievert becquerel gamma radiation`: returned mathematical gamma-distribution/function declarations and `DimEnergy.joule`, but no ionizing-radiation activity/dose interface. No candidate from this query was used.
- Natural-language query `dimensionful SI physical quantities mass length time energy area electron volt`: used `UnitChoices.SI`, `Dimension`, `Dimensionful`, `DimEnergy`, and `DimEnergy.electronVolt`.
- Likely-name query `Dimensionful WithDim DimArea DimEnergy electronVolt Real.pi`: used `Dimensionful`, `WithDim`, `DimArea`, `Dimension`, and `DimEnergy`.
- Likely-name query `Dimension.L𝓭 Dimension.T𝓭 Dimension.M𝓭`, followed by `Dimension.M𝓭 mass dimension`: used `Dimension.L𝓭`, `Dimension.T𝓭`, and `Dimension.M𝓭`.
- Likely-name query `Real.pi`: used `Real.pi`.

Source, module, and docstring data were fetched for the candidates actually used: `UnitChoices.SI` (ID 394270), `Dimensionful` (394284), `WithDim` (394425), `Dimension.L𝓭` (394324), `Dimension.T𝓭` (394330), `Dimension.M𝓭` (394336), `DimArea` (394411), `DimEnergy` (394468), `DimEnergy.electronVolt` (394470), and `Real.pi` (146728).

## Grounded Physlib/Mathlib names

- Physlib unit core: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`, and `UnitChoices.SI`.
- Physlib quantities/constants: `DimArea`, `DimEnergy`, and `DimEnergy.electronVolt`.
- Mathlib geometry constant: `Real.pi`, grounded to `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` and used in the spherical-area denominator.

The imports in the assigned file are the modules needed by those grounded names: `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`, `Physlib.Units.WithDim.Area`, and `Physlib.Units.WithDim.Energy`.

## Local abstractions introduced

- `DimLength`, `DimTime`, `DimMass`, `DimActivity`, and `DimSpecificEnergy` specialize Physlib's `Dimensionful (WithDim ...)` construction. They retain length, time, mass, inverse-time, and energy-per-mass dimensions and are not scalar aliases.
- `Nuclide` and `Cobalt60Exposure` retain radionuclide identity, geometry, activity, exposure duration, both gamma lines, partition fractions, and radiation-weighting role.
- `WholeBodyDose` distinguishes absorbed from gamma-equivalent specific energy; `DoseComputation` records physical intermediates without identifying an answer.
- Unit-named scalar functions are explicit readouts of dimensionful quantities rather than replacements for those quantities.
- `MatchesProblemData` separates source/figure measurements from `ValidDosePhysics`, the smallest local law interface needed because no matching library radiation API was found.
- `DoseAnswerChoice` and `answerValueMilliSievert` preserve the multiple-choice metadata separately from the physical calculation.

## Grounding gaps and redraft requests

- LeanExplore exposed no ready-made Physlib declarations for radioactive activity, becquerel/curie conversion, absorbed/equivalent radiation dose, cobalt-60 emissions, or isotropic point-source dose laws. The dimension-safe local abstractions and explicit governing laws fill these gaps without assuming the target.
- No redraft is requested: the review-gate reason is missing post-formalization evidence, and the source/law/answer audit found no semantic defect requiring a statement change.
- `.archon/AGENTS.md` is absent. The available `.archon/prover-modes/physics-formalize.md` and the explicit task instructions supplied the role requirements.
- The `archon` executable is not available on `PATH`, so the optional read-only dependency-graph query could not run.
- The primary image was inspected directly. It shows a central point source with radial arrows, a concentric dashed circle, a worker, and a radial segment labeled `4.0 m`, supporting the figure readout and isotropic geometry.
- The blueprint chapter was not edited with `\leanok`: the task expressly restricts writes to the assigned Lean file and this result file and separately prohibits blueprint edits.

## Verification

- `archon-lean-lsp` reports exactly one diagnostic: the expected `declaration uses 'sorry'` warning on the autoformalization target.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0619.lean` exits successfully with the same single expected `sorry` warning.
